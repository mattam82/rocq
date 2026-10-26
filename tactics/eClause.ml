(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Nameops
open Termops
open Constr
open Context
open EConstr
open Vars
open Evarutil
open Tactypes
open Pretype_errors

(** {6 Evar-based clauses} *)

type hole = {
  hole_evar : EConstr.constr;
  hole_type : EConstr.types;
  hole_deps  : bool;
  hole_name : Name.t;
  hole_evar_key : Evar.t;
}

type clause = {
  cl_holes : hole list;
  (** The holes of the clause. *)
  cl_concl : types;
  (** The conclusion: an evar applied to some terms *)
  cl_concl_occs : Evarconv.occurrences_selection option;
  (** The occurrences of the terms to be abstracted when unifying *)
  cl_val   : constr;
  (** The value the clause was built from, applied to holes *)
}

let debug_clenv = CDebug.create ~name:"clenv" ()

(* When set, arguments of an applied lemma that only appear in its
   conclusion and are not instantiated by unification with the goal are turned
   into new goals rather than being reported as unresolved, as the meta-based
   implementation of apply did. *)
let { Goptions.get = legacy_apply_dependency } =
  Goptions.declare_bool_option_and_ref
    ~key:["Legacy";"Apply";"Dependency"]
    ~value:false
    ()

let pr_clause ?(with_evars=false) env sigma clause =
  let prc = Termops.Internal.print_constr_env env sigma in
  let pr_hole hole = Pp.(Name.print hole.hole_name ++ str" : " ++ prc hole.hole_evar ++
    str"(dep:" ++ Pp.bool hole.hole_deps ++ str")") in
  Pp.(h (str"Value: " ++ prc clause.cl_val ++
         str" : " ++ prc clause.cl_concl ++ fnl () ++
         str"Holes: " ++ prlist_with_sep spc pr_hole clause.cl_holes ++
         if with_evars then pr_evar_map (Some 0) env sigma else mt ()))

let qhyp_eq h1 h2 = match h1, h2 with
| NamedHyp n1, NamedHyp n2 -> lident_eq n1 n2
| AnonHyp i1, AnonHyp i2 -> Int.equal i1 i2
| _ -> false

let check_bindings bl =
  match List.duplicates qhyp_eq (List.map (fun {CAst.v=x} -> fst x) bl) with
    | NamedHyp s :: _ ->
        user_err ?loc:s.CAst.loc
          Pp.(str "The variable " ++ Id.print s.CAst.v ++
              str " occurs more than once in binding list.");
    | AnonHyp n :: _ ->
        user_err
          Pp.(str "The position " ++ int n ++
              str " occurs more than once in binding list.")
    | [] -> ()

let explain_no_such_bound_variable mvl {CAst.v=id;loc} =
  let open Pp in
  let expl = match mvl with
  | [] -> str "(no bound variables at all in the expression)."
  | [id] -> str "(possible name is: " ++ Id.print id ++ str ")."
  | _ -> str "(possible names are: " ++ pr_enum Id.print mvl ++ str ")."
  in
  user_err ?loc (str "No such bound variable " ++ Id.print id ++ spc () ++ expl)

let error_not_right_number_missing_arguments n =
  user_err
    Pp.(strbrk "Not the right number of missing arguments (expected " ++
        int n ++ str ").")

let hole_source = function
  | Anonymous -> Loc.tag Evar_kinds.GoalEvar
  | Name id   -> Loc.tag @@ Evar_kinds.VarInstance id

let make_prod_evar ctx sigma ~args na t1 t2 =
  (* Add a name to the evar if it comes from a named binder to make the
     goal focusable. *)
  let name = match na.binder_name with
  | Name id when Evd.generate_goal_names () ->
    Evarutil.next_evar_name (Namegen.IntroIdentifier id)
  | _ -> None
  in
  let (sigma, evk) = new_pure_evar ~src:(hole_source na.binder_name) ?name
      ~typeclass_candidate:false ctx sigma
      ~relevance:na.binder_relevance t1
  in
  (* Do not mark any evar as a future goal at this point *)
  let sigma = Evd.remove_future_goal sigma evk in
  let ev = mkEvar (evk, args) in
  let dep = not (noccurn sigma 1 t2) in
  let hole = {
    hole_evar = ev;
    hole_type = t1;
    hole_deps = dep;
    (* We fix it later *)
    hole_name = na.binder_name;
    hole_evar_key = evk;
  } in
  let t2 = subst1 ev t2 in
  sigma, hole, t2

(** Stripping params on applications of primitive projections *)
(* MD This is duplicated from `Hints` *)
let strip_params env sigma c =
  match EConstr.kind sigma c with
  | App (f, args) ->
    (match EConstr.kind sigma f with
     | Const (cst,u) ->
       (match Structures.PrimitiveProjections.find_opt_with_relevance (cst,u) with
        | Some (p,r) ->
          let p = Projection.make p false in
          let npars = Projection.npars p in
          if Array.length args > npars then
            mkApp (mkProj (p, r, args.(npars)),
                   Array.sub args (npars+1) (Array.length args - (npars + 1)))
          else c
        | None -> c)
     | _ -> c)
  | _ -> c

(** Template polymorphism: when creating a clause out of a template
    polymorphic constructor, we refresh the type of the template arguments
    with fresh universe levels. This prevents adding spurious global
    constraints between the argument types and the global default template
    level (same as in [Clenv]). *)
let get_template env sigma c =
  let (hd, args) = EConstr.decompose_app sigma c in
  match EConstr.destRef sigma hd with
  | GlobRef.ConstructRef (ind, i), u when Environ.template_polymorphic_ind ind env ->
    let (mib, mip) = Inductive.lookup_mind_specif env ind in
    let templ = match mib.Declarations.mind_template with
    | None -> assert false
    | Some t -> t.template_param_arguments
    in
    Some (ind, List.skipn_at_best (Array.length args) templ)
  | _ -> None
  | exception DestKO -> None

let refresh_template_constraints env sigma ind c =
  let mib = Environ.lookup_mind (fst ind) env in
  let ctx = (Option.get mib.mind_template).template_context in
  let cstrs0 = UVars.UContext.constraints @@ UVars.AbstractContext.repr ctx in
  if PConstraints.is_empty cstrs0 then sigma
  else
    let _, allargs = decompose_app sigma c in
    let allargs = Array.map (fun c -> Retyping.get_judgment_of env sigma c) allargs in
    let sigma, univs = Typing.get_template_parameters env sigma ind allargs in
    let cstrs, _, _ = Inductive.instantiate_template_universes mib univs in
    Evd.add_univ_constraints sigma (PConstraints.univs cstrs)

let make_evar_clause env sigma ?len ?occs c t =
  let bound = match len with
  | None -> -1
  | Some n -> assert (0 <= n); n
  in
  let template = get_template env sigma c in
  let template_args = match template with Some (_, args) -> args | None -> [] in
  let rec clrec templ (sigma, holes) inst n t =
    if n = 0 then (sigma, holes, t)
    else match EConstr.kind sigma t with
    | Cast (t, _, _) -> clrec templ (sigma, holes) inst n t
    | Prod (na, t1, t2) ->
      (* Share the evar instances as we are living in the same context *)
      let inst, ctx, args, subst = match inst with
      | None ->
        (* Dummy type *)
        let ctx, _, args, subst = push_rel_context_to_named_context env sigma mkProp in
        Some (ctx, args, subst), ctx, args, subst
      | Some (ctx, args, subst) -> inst, ctx, args, subst
      in
      let sigma, t1, templ = match templ with
      | [] -> sigma, t1, templ
      | None :: templ -> sigma, t1, templ
      | Some _ :: templ ->
        let decls, _ = Reductionops.dest_arity env sigma t1 in
        let sigma, s = Evd.new_univ_level_variable Evd.univ_flexible_alg sigma in
        let t1 = EConstr.it_mkProd_or_LetIn (EConstr.mkType (Univ.Universe.make s)) decls in
        sigma, t1, templ
      in
      let sigma, hole, t2 = make_prod_evar ctx sigma ~args na (csubst_subst sigma subst t1) t2 in
      clrec templ (sigma, hole :: holes) inst (pred n) t2
    | LetIn (na, b, _, t) -> clrec templ (sigma, holes) inst n (subst1 b t)
    | _ -> (sigma, holes, t)
  in
  let (sigma, holes, t) = clrec template_args (sigma, []) None bound t in
  let holes = List.rev holes in
  let v = applist (c, List.map (fun h -> h.hole_evar) holes) in
  let sigma = match template with
  | None -> sigma
  | Some (ind, _) -> refresh_template_constraints env sigma ind v
  in
  let c = strip_params env sigma v in
  let clause = { cl_holes = holes; cl_val = c;
                 cl_concl = t; cl_concl_occs = occs } in
  (sigma, clause)

let hole_with_name holes ({CAst.v=id} as lid) =
  let map h = match h.hole_name with
  | Anonymous -> None
  | Name id' -> if Id.equal id id' then Some h else None
  in
  let hole = List.map_filter map holes in
  match hole with
  | [] ->
    let fold h accu = match h.hole_name with
      | Anonymous -> accu
      | Name id -> id :: accu
    in
    let mvl = List.fold_right fold holes [] in
    explain_no_such_bound_variable mvl lid
  | [h] -> h
  | _ ->
    user_err ?loc:lid.CAst.loc
      Pp.(str "Binder name \"" ++ Id.print id ++
        str "\" occurs more than once in clause.")

(* let nth_anonymous holes n =
  let rec hole holes n =
    match holes, n with
    | h :: holes, n when h.hole_name <> Anonymous -> hole holes n
    | h :: holes, 0 -> h
    | h :: holes, n -> hole holes (pred n)
    | [], _ -> user_err (str "No such binder.")
  in hole holes (pred n) *)

let hole_of_binder holes = function
| NamedHyp s -> hole_with_name holes s
| AnonHyp n ->
  try
    let nondeps = List.filter (fun hole -> not hole.hole_deps) holes in
    List.nth nondeps (pred n)
  with e when CErrors.noncritical e ->
    user_err Pp.(str "No such binder.")

let define_with_type env sigma ?flags ev c ty =
  let t = Retyping.get_type_of env sigma ev in
  let ty =
    match ty with
    | Some t -> t
    | None -> Retyping.get_type_of env sigma c in
  let j = Environ.make_judge c ty in
  let (sigma, j, _trace) = Coercion.inh_conv_coerce_to ~program_mode:false ~resolve_tc:true env sigma ?flags j t in
  let (ev, _) = destEvar sigma ev in
  let sigma = Evd.define ev j.Environ.uj_val sigma in
  sigma

let warn_unused_with_argument =
  CWarnings.create ~name:"unused-with-argument" ~category:CWarnings.CoreCategories.tactics
    Pp.(fun na -> str"Ignoring 'with' argument for binder " ++ Name.print na ++ str", already solved by unification.")

let try_define_with_type env sigma ev c ty =
  if isEvar sigma ev.hole_evar then
    define_with_type env sigma ev.hole_evar c ty
  else
    (warn_unused_with_argument ev.hole_name; sigma)

let apply_delayed_bindings env delayed sigma =
  List.fold_right (fun (ev,arg) sigma -> try_define_with_type env sigma ev arg None) delayed sigma

(** This requires to look at the evar even if it is defined *)
let hole_goal h = h.hole_evar_key

let clenv_advance sigma clenv =
  let { cl_concl; cl_holes; cl_val; cl_concl_occs } = clenv in
  let advance h =
    let h' = whd_evar sigma h.hole_evar in
    if Constr.equal (EConstr.Unsafe.to_constr h') (EConstr.Unsafe.to_constr h.hole_evar)
    then Some h
    else
      let ev = hole_goal h in
      match Proofview.Unsafe.advance sigma ev with
      | Some ev' ->
         let na =
           match Evd.evar_ident ev' sigma with
           | Some p -> Name (Libnames.basename p)
           | None -> h.hole_name
         in
         Some { h with hole_evar = h'; hole_name = na; hole_evar_key = ev' }
      | None -> None
  in
  let holes = List.map_filter advance cl_holes in
    if holes == cl_holes then clenv
    else
      { cl_holes = holes;
        cl_concl = nf_evar sigma cl_concl;
        cl_val = nf_evar sigma cl_val;
        cl_concl_occs }

let hole_evar sigma hole = fst (destEvar sigma hole.hole_evar)

let hole_type env sigma hole =
  let concl = Evd.evar_concl (Evd.find_undefined sigma (hole_evar sigma hole)) in
  Reductionops.nf_betaiota env sigma (Evarutil.nf_evar sigma concl) (* MD is normalizing useful here? *)

let clenv_recompute_deps env sigma ~hyps_only clause =
  let fold h holes =
    if h.hole_deps then
      (* Some subsequent term uses the hole *)
      let (ev, _) = destEvar sigma h.hole_evar in
      let is_dep hole = occur_evar sigma ev (hole_type env sigma hole) in
      let in_hyp = List.exists is_dep holes in
      (* Beta-iota normalize the conclusion, which may have been instantiated
         by higher-order unification with a constant predicate. *)
      let in_ccl = occur_evar sigma ev (Reductionops.nf_betaiota env sigma clause.cl_concl) in
      let dep = if hyps_only then in_hyp && not in_ccl else in_hyp || in_ccl in
      let h = { h with hole_deps = dep } in
      h :: holes
    else
      (* The hole does not occur anywhere *)
      h :: holes
  in
  let holes = List.fold_right fold clause.cl_holes [] in
  { clause with cl_holes = holes }

let solve_evar_clause env sigma ~hyps_only clause b =
  let define_if_known_type (sigma,delayed) ev arg =
    let head, _ = decompose_app sigma ev.hole_type in
    if EConstr.isEvar sigma head then
      (debug_clenv Pp.(fun () -> Pp.str"Delaying instantiation of " ++ Name.print ev.hole_name);
      (sigma, (ev,arg) :: delayed))
    else
      try
        (define_with_type env sigma ev.hole_evar arg None, delayed)
      with
      | PretypeError (_,_,ActualTypeNotCoercible (_,_,
          (NotClean _ | ConversionFailed _))) as e ->
          raise e
      | e when precatchable_exception e ->
          (sigma, (ev,arg) :: delayed)
  in
  match b with
  | NoBindings -> sigma, [], clause
  | ImplicitBindings largs ->
    let clause = if hyps_only then clenv_recompute_deps env sigma ~hyps_only clause else clause in
    let evs, holes' = List.partition (fun h -> h.hole_deps) clause.cl_holes in
    let len = List.length evs in
    if Int.equal len (List.length largs) then
      let sigma, delayed = List.fold_left2 define_if_known_type (sigma,[]) evs largs in
      let clause = { clause with cl_holes = holes' } in
      sigma, delayed, clenv_advance sigma clause
    else
      error_not_right_number_missing_arguments len
  | ExplicitBindings lbind ->
    let () = check_bindings lbind in
    let fold (sigma, delayed, holes) {CAst.v=(binder, c)} =
      let ev = hole_of_binder clause.cl_holes binder in
      let rem ev' = EConstr.eq_constr sigma ev.hole_evar ev'.hole_evar in
      let holes = List.remove_first rem holes in
      let sigma, delayed = define_if_known_type (sigma,delayed) ev c in
      sigma, delayed, holes
    in
    let sigma, delayed, holes = List.fold_left fold (sigma,[],clause.cl_holes) lbind in
    let clause = { clause with cl_holes = holes } in
    sigma, delayed, clenv_advance sigma clause

let make_clenv_from_env env sigma ?len ?occs (c, t) =
  make_evar_clause env sigma ?len ?occs (strip_outer_cast sigma c) t

let make_clenv_bindings env sigma ?len ?occs p ~hyps_only b =
  let sigma, cle = make_clenv_from_env env sigma ?len ?occs p in
  solve_evar_clause env sigma ~hyps_only cle b

let clenv_indep_holes c =
  let holes = c.cl_holes in
  let filter h = not h.hole_deps in
  List.filter filter holes

let clenv_concl cl = cl.cl_concl
let clenv_val   cl = cl.cl_val
let clenv_holes cl = cl.cl_holes

let clenv_dep_holes clenv =
  let holes = clenv_holes clenv in
  List.filter (fun h -> h.hole_deps) holes

exception NotExtensibleClause
exception NoSuchBinding

let clenv_dest_prod env sigma
  { cl_concl = concl; cl_holes = holes; cl_val = v; cl_concl_occs = occs } =
  let typ = Reductionops.whd_all env sigma concl in
  let rec clrec typ = match EConstr.kind sigma typ with
    | Cast (t,_,_) -> clrec t
    | Prod (na,t,u) ->
      let ctx, _, args, subst = push_rel_context_to_named_context env sigma mkProp in
      make_prod_evar ctx sigma ~args na (csubst_subst sigma subst t) u
    | _ -> raise NotExtensibleClause
  in
  let sigma, hole, typ' = clrec typ in
  let v = strip_params env sigma (applist (v, [hole.hole_evar])) in
  let occs' =
    match occs with
    | None -> None
    | Some (f, occs) -> Some (f, occs @ [Evarconv.default_occurrence_selection])
  in
  let clause =
    { cl_holes = holes @ [hole]; cl_val = v;
      cl_concl = typ'; cl_concl_occs = occs' }
  in sigma, clause

let clenv_map_concl f clenv =
  let concl = clenv.cl_concl in
  { clenv with cl_concl = f concl }

let clenv_unify_type ?holes env sigma flags hole occs ty =
  (* Give priority to second-order matching which avoids falling back
     to it with unfolded terms through evar_conv. *)
  let ev, l = decompose_app sigma hole in
  (* Is the head of the conclusion a hole of the clause (as opposed to an
     existential variable coming e.g. from the implicit arguments of the
     applied term, which the meta-based implementation treated
     first-order)? *)
  let is_hole ev = match holes with
    | None -> true
    | Some holes -> Evar.Set.mem (fst (destEvar sigma ev)) holes
  in
  let hd, l' = decompose_app sigma ty in
  let is_explicit_pattern =
    if Array.length l == Array.length l' then
      try ignore(decompose_lambda_n_decls sigma (Array.length l) hd); true
      with e -> not (isEvar sigma ev)
    else not (isEvar sigma ev)
  in
  (* In case the clause is not higher-order (has no occurrences selected)
     or the type we're unifying with is an explicit predicate
     applied to the right number of arguments, we favor direct
     unification. *)
  match occs with
  | Some (f, occs) when not is_explicit_pattern ->
     let (evk, subst as ev) = destEvar sigma ev in
     let sigma, ev' =
       Evardefine.evar_absorb_arguments env sigma ev (Array.to_list l) in
     let argoccs = List.init (SList.length (snd ev)) (fun _ -> Evarconv.default_occurrence_selection) in
     let f, occs =
       (* We are lenient here, allowing more occurrences to be specified than
           the actual arguments of the evar. Helps dealing with eliminators we
           don't know the arity of (e.g. dependent or not). *)
       let () =
         if not (Array.length l <= List.length occs) then
           user_err (Pp.str"Clause unification: occurrence list does not match argument list")
       in (f, List.firstn (Array.length l) occs)
     in
     let occs = List.rev (argoccs @ occs) in
     let sigma, b =
       Evarconv.second_order_matching flags env sigma ev' (f, occs) ty
     in
     if not b then
       let reason = ConversionFailed (env,hole,ty) in
       Pretype_errors.error_cannot_unify env sigma ~reason (hole, ty)
     else
       (* Ensure we did actually find a solution *)
       Evarconv.solve_unif_constraints_with_heuristics
         ~flags ~with_ho:true env sigma
  | _ ->
     (* Higher-order unification is only used as a fallback when the head of
        the conclusion is a hole of the clause, as [w_unify] did for
        meta-headed conclusions: for other conclusions (e.g. headed by an
        existential variable coming from the elaboration of the applied
        term), only first-order unification was used. *)
     let ho_allowed = isEvar sigma ev && is_hole ev in
     let ho e =
       if not ho_allowed then raise e
       else
       let sigma = Evarutil.add_unification_pb (Conversion.CUMUL,env,hole,ty) sigma in
        Evarconv.solve_unif_constraints_with_heuristics
          ~flags ~with_ho:true env sigma
     in
     let open Evarsolve in
     (* When the conclusion is an evar applied to arguments (as for
        elimination-like lemmas), favor second-order matching over the
        first-order decomposition of the application, as [w_unify] did. *)
     (* Emulate [w_unify_to_subterm_list] with allow_K disabled (the flags of
        apply): each argument must unify with some closed subterm of the goal,
        bare evars cannot be abstracted over, and two arguments must not be
        matched to the same subterm (non-linear unification). Arguments are
        processed from the last one, so that the evars of the first arguments
        get instantiated by the last ones. *)
     let find_arg_instances sigma =
       let exception Found of Evd.evar_map * constr in
       let test = Evarconv.default_occurrence_test ~allowed_evars:flags.allowed_evars flags.subterm_ts in
       let find sigma c =
         let rec aux t =
           let () =
             if Vars.closed0 sigma t && not (isEvar sigma t) then
               match test env sigma c t with
               | (true, sigma') -> raise (Found (sigma', t))
               | (false, _) -> ()
               | exception e when CErrors.noncritical e -> ()
           in
           EConstr.iter sigma aux t
         in
         match aux ty with
         | () -> None
         | exception Found (sigma', t) -> Some (sigma', t)
       in
       let fold c acc = match acc with
         | None -> None
         | Some (sigma, found) ->
           let c = whd_evar sigma c in
           if isEvar sigma c then None
           else match find sigma c with
             | None -> None
             | Some (sigma', t) ->
               if List.exists (fun t' -> EConstr.eq_constr sigma' t t') found then None
               else Some (sigma', t :: found)
       in
       Array.fold_right fold l (Some (sigma, []))
     in
     let so_first () =
       (* When all the arguments are variables, this is a Miller pattern which
          is handled by evar_conv_x (in tactic mode, restricting the evars of
          the solution so that it eta-reduces). *)
       let is_pattern = Array.for_all (fun c -> isVar sigma c || isRel sigma c) l in
       if isEvar sigma ev && is_hole ev && not (Array.is_empty l) && not is_pattern && not is_explicit_pattern then
         match find_arg_instances sigma with
         | None -> None
         | Some (sigma, _) ->
         match Evarconv.second_order_matching_with_args flags env sigma true
                 Conversion.CUMUL (destEvar sigma ev) l ty with
         | Success sigma' ->
           (try Some (Evarconv.solve_unif_constraints_with_heuristics
                        ~flags ~with_ho:true env sigma')
            with e when CErrors.noncritical e -> None)
         | UnifFailure _ -> None
         | exception e when CErrors.noncritical e -> None
       else None
     in
     match so_first () with
     | Some sigma -> sigma
     | None ->
     (* Try normal unification first, if that fails use heuristics + higher-order unif *)
     let npbs = List.length (Evd.conv_pbs sigma) in
     match Evarconv.evar_conv_x flags env sigma Conversion.CUMUL hole ty with
     | Success sigma' ->
        (try Evarconv.solve_unif_constraints_with_heuristics
               ~flags ~with_ho:false env sigma'
         with e when CErrors.noncritical e ->
           (* The goal may already carry postponed problems that cannot be
              solved yet, which the meta-based implementation never looked
              at: this is not a failure of this unification if it
              introduced no new problem. *)
           if List.length (Evd.conv_pbs sigma') <= npbs then sigma'
           else ho e)
     | UnifFailure (sigma', reason) ->
       if ho_allowed then ho (Evarconv.UnableToUnify (sigma', reason))
       else
         (* Same error as the one raised by the heuristics on the postponed
            problem *)
         Pretype_errors.error_cannot_unify env sigma' ~reason (hole, ty)


let clenv_unify_concl env sigma flags ty clenv =
  let concl, occs = clenv.cl_concl, clenv.cl_concl_occs in
  let holes = Evar.Set.of_list (List.map (fun h -> h.hole_evar_key) clenv.cl_holes) in
  let sigma = clenv_unify_type ~holes env sigma flags concl occs ty in
  sigma, clenv_advance sigma clenv

(* [clenv_chain mv clenv clenv']
 *
 * Resolves the value of "mv" (which must be undefined) in clenv to be
 * the template of clenv' be the value "c", applied to "n" fresh
 * metavars, whose types are chosen by destructing "clf", which should
 * be a clausale forme generated from the type of "c".  The process of
 * resolution can cause unification of already-existing metavars, and
 * of the fresh ones which get created.  This operation is a composite
 * of operations which pose new metavars, perform unification on
 * terms, and make bindings.

   Otherwise said, from

     [clenv] = [env;sigma;metas |- c:T]
     [clenv'] = [env';sigma';metas' |- d:U]
     [mv] = [mi] of type [Ti] in [metas]

   then, if the unification of [Ti] and [U] produces map [rho], the
   chaining is [env';sigma';rho'(metas),rho(metas') |- c:rho'(T)] for
   [rho'] being [rho;mi:=d].

   In particular, it assumes that [env'] and [sigma'] extend [env] and [sigma].
*)

let hole_def sigma h =
  match h.hole_name with
  | Name id ->
     let res = nf_evar sigma h.hole_evar in
     if isEvar sigma res then
       Some (fst (destEvar sigma res), id)
     else None
  | Anonymous -> None

let fchain_flags () =
  { (Unification.default_unify_flags ()) with
    allow_K_in_toplevel_higher_order_unification = true }

let clenv_chain ?(holes_order=true) ?(flags=fchain_flags ()) ?occs
                env sigma h cl nextcl =
  let flags = Unification.flags_of flags in
  let sigma, cl =
    match occs with
    | None -> define_with_type env sigma ~flags
                 h.hole_evar nextcl.cl_val (Some nextcl.cl_concl), cl
    | Some _ ->
       let ty = hole_type env sigma h in
       let ty' = nextcl.cl_concl in
       let sigma = clenv_unify_type env sigma flags ty occs ty' in
       let (ev, _) = destEvar sigma h.hole_evar in
       let sigma = Evd.define ev nextcl.cl_val sigma in
       sigma, cl
  in
  let sigma, clholes =
    let nextclholes =
      List.map_filter (fun h -> hole_def sigma h) nextcl.cl_holes
    in
    List.fold_left_map (fun sigma h ->
        try
          let id = List.assoc_f Evar.equal (hole_goal h) nextclholes in
          let sigma =
            if Evd.is_undefined sigma (hole_goal h) then
              Evd.update_source sigma (hole_goal h) (Loc.tag @@ Evar_kinds.VarInstance id)
            else sigma
          in
          sigma, { h with hole_name = Name id }
        with Not_found -> sigma, h) sigma cl.cl_holes
  in
  let holes' =
    if holes_order then
      clholes @ nextcl.cl_holes
    else
      nextcl.cl_holes @ clholes
  in
  let cl = { cl with cl_holes = holes' } in
  sigma, clenv_advance sigma cl

let clenv_chain_last ?(flags=fchain_flags ()) env sigma c cl =
  let h = try List.last cl.cl_holes with Failure _ -> raise NoSuchBinding in
  let sigma = define_with_type env sigma ~flags:(Unification.flags_of flags) h.hole_evar c None in
  sigma, clenv_advance sigma cl

let check_evar_clause env sigma sigma' eq_clause =
  let f h = if h.hole_deps then Some h.hole_evar_key else None in
  match Tacticals.check_evar_list env sigma' (Evar.Set.of_list (List.map_filter f eq_clause.cl_holes)) sigma with
  | [] -> ()
  | evkl ->
    let filter h = if List.exists (Evar.equal h.hole_evar_key) evkl then Some h.hole_name else None in
    let bindings = List.map_filter filter eq_clause.cl_holes in
    Loc.raise (Logic.RefinerError (env, sigma, UnresolvedBindings bindings))

(** {6 Refinement tactics based on clauses} *)

let dft = Unification.default_unify_flags

let holes_goals sigma holes =
  List.map (fun h -> fst (destEvar sigma h.hole_evar)) holes

let unresolved_dep_holes sigma ?origsigma ~strict clenv =
  let holes = clenv_dep_holes clenv in
  match origsigma with
  | None -> holes
  | Some origsigma ->
     let origevars = Evar.Map.domain (Evd.undefined_map origsigma) in
     let reachable = Evarutil.reachable_from_evars sigma origevars in
     let filter h = not (Evar.Set.mem (fst (destEvar sigma h.hole_evar)) reachable) in
     (match List.filter filter holes with
      | [] -> []
      | holes when strict -> holes
      | holes ->
        (* Unless [strict] is set, holes occurring in the instances of evars
           that were undefined before the refinement are allowed as well: they
           correspond to the metas that the meta-based unification turned into
           evars when instantiating an existing evar with a term containing
           metas ([apply] accepted them, [apply in] did not). *)
        let occurring =
          Evar.Set.fold (fun ev acc ->
              match Evd.find_defined sigma ev with
              | None -> acc
              | Some evi ->
                let Evd.Evar_defined b = Evd.evar_body evi in
                Evar.Set.union acc (Evarutil.undefined_evars_of_term sigma b))
            origevars Evar.Set.empty
        in
        let filter h = not (Evar.Set.mem (fst (destEvar sigma h.hole_evar)) occurring) in
        List.filter filter holes)

let check_dep_holes env sigma ?origsigma ?(strict=false) clenv =
  match unresolved_dep_holes sigma ?origsigma ~strict clenv with
  | [] -> ()
  | holes ->
    raise (Logic.RefinerError (env, sigma, Logic.UnresolvedBindings
                                 (List.map (fun h -> h.hole_name) holes)))

let clenv_check_dep_holes with_evars env sigma ?origsigma ?strict clenv =
  let holes = clenv_dep_holes clenv in
  if not with_evars then
    match check_dep_holes env sigma ?origsigma ?strict clenv with
    | () -> Proofview.tclUNIT (holes_goals sigma holes)
    | exception (Logic.RefinerError _ as e) -> Proofview.tclZERO e
  else Proofview.tclUNIT (holes_goals sigma holes)

let clenv_solve_clause_constraints ?(flags=dft ()) ~with_ho clenv =
  let open Proofview in
  let open Proofview.Notations in
  tclENV >>= fun env ->
  tclEVARMAP >>= fun sigma ->
    try
      let flags = Unification.flags_of flags in
      let sigma' =
        Evarconv.solve_unif_constraints_with_heuristics env ~flags ~with_ho sigma
      in Unsafe.tclEVARS sigma' <*> tclUNIT (clenv_advance sigma' clenv)
    with e when CErrors.noncritical e -> tclZERO e

(** Compatibility: dependent typeclasses holes which previously resulted from turning metas into evars
    should be resolved. *)
let get_dependent_typeclass_holes env sigma clenv =
  let evs = List.map_filter (fun h ->
    let ty = hole_type env sigma h in
    if h.hole_deps && Typeclasses.is_maybe_class_type env sigma ty then Some (hole_evar sigma h)
    else None) clenv.cl_holes
  in Evar.Set.of_list evs

let clenv_refine_gen ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true) ?(with_ho=true)
                     ?(legacy_deps=false) ?origsigma ?strict flags (sigma, clenv) =
  let open Proofview in
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma, clenv =
    try
      let sigma = Evarconv.solve_unif_constraints_with_heuristics ~flags ~with_ho env sigma in
      sigma, clenv_advance sigma clenv
    with e when CErrors.noncritical e -> sigma, clenv in
  let sigma, clenv =
    if with_classes then
      let hole_tcs = get_dependent_typeclass_holes env sigma clenv in
      let tcs = Evd.get_typeclass_evars sigma in
      let sigma = Evd.set_typeclass_evars sigma (Evar.Set.union tcs hole_tcs) in
      let () = debug_clenv (fun () -> Pp.(str"Solving typeclasses:" ++ pr_clause ~with_evars:true env sigma clenv)) in
      let sigma = Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars
        (* Don't split as this can result in typeclasses not failing due
           to initial holes not being marked as "mandatory". *)
        ~fail:(not with_evars) env sigma
      in
      let sigma = Evd.set_typeclass_evars sigma tcs in
      sigma, clenv_advance sigma clenv
    else sigma, clenv
  in
  let run shelf sigma =
    (* Declare the future goals here, as they should become subgoals of this refine. *)
    let declare_goal sigma h =
      let ev, _ = destEvar sigma h.hole_evar in
      if List.mem_f Evar.equal ev shelf then sigma
      else Evd.declare_future_goal ev sigma
    in
    let sigma = List.fold_left declare_goal sigma (clenv_holes clenv) in
    let sigma = Evd.shelve sigma shelf in
    let v = Reductionops.nf_betaiota env sigma (clenv_val clenv) in
    sigma, v
  in
  let reduce_goal gl =
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    let glev = Proofview.Goal.goal gl in
    (* For compatibility: beta iota reduction *)
    let concl = Reductionops.clos_norm_flags RedFlags.betaiota env sigma concl in
    let sigma = Evd.downcast glev concl sigma in
    let sigma = Typeclasses.make_unresolvables (fun ev -> Evar.equal ev glev) sigma in
    Proofview.Unsafe.tclEVARS sigma
  in
  let () = debug_clenv (fun () -> Pp.(str"Checking dependent holes are resolved: " ++ pr_clause env sigma clenv)) in
  (* With the legacy dependency semantics, holes appearing only in the
     conclusion are not reported as unresolved (they are shelved below, as
     with eapply, when they appear in other goals). *)
  let check_clenv =
    if legacy_deps then clenv_recompute_deps env sigma ~hyps_only:true clenv else clenv in
  Proofview.Unsafe.tclEVARS sigma <*>
    clenv_check_dep_holes with_evars env sigma ?origsigma ?strict check_clenv >>= (fun _ ->
      let deps = holes_goals sigma (clenv_dep_holes clenv) in
      let () = debug_clenv (fun () -> Pp.str"Refining the goal") in
      let shelf = if shelve_subgoals then deps else [] in
      (Refine.refine ~typecheck:false (run shelf)) <*>
      Unsafe.tclGETSHELF >>= fun shelf ->
      Unsafe.tclGETGOALS >>= fun gls ->
      let () = debug_clenv Pp.(fun () -> str"New shelf: " ++ prlist_with_sep spc Evar.print shelf ++ fnl ()
        ++ str "New goals " ++ prlist_with_sep spc (fun x -> Evar.print (drop_state x)) gls) in
      Proofview.Goal.enter reduce_goal)
  end

let clenv_unify_concl_tac flags clenv k =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  match clenv_unify_concl env sigma flags concl clenv with
  | (sigma, clenv) -> k (sigma, clenv)
  | exception Evarconv.UnableToUnify (evd, reason) ->
    let ex = Pretype_errors.(PretypeError (env, evd,
        CannotUnify (concl, clenv_concl clenv, Some reason))) in
    Proofview.tclZERO ex
  end

let clenv_refine_bindings
    ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true) ?with_ho
    ?(flags=dft ()) ~hyps_only b ?origsigma clenv =
  let open Proofview in
  let open Proofview.Notations in
  let flags = Unification.flags_of flags in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let sigma, delayed, clenv =
      solve_evar_clause env sigma ~hyps_only clenv b
    in
    debug_clenv Pp.(fun () -> str"Solved evar clause" ++ pr_clause env sigma clenv);
    (Unsafe.tclEVARS sigma) <*>
    (clenv_unify_concl_tac flags clenv
      (fun (sigma, clenv) ->
        debug_clenv (fun () -> Pp.str"Unified conclusion of clause with goal conclusion");
        try
          let clenv = clenv_recompute_deps env sigma ~hyps_only:false clenv in
          debug_clenv (fun () -> Pp.str"Recomputed dependencies");
          let sigma = apply_delayed_bindings env delayed sigma in
          debug_clenv (fun () -> Pp.str"Applied delayed bindings");
          let legacy_deps = legacy_apply_dependency () in
          clenv_refine_gen ~with_evars ~with_classes ~shelve_subgoals ?with_ho ~legacy_deps ?origsigma
                         flags (sigma, clenv)
        with e when Pretype_errors.precatchable_exception e -> Proofview.tclZERO e))
  end

let clenv_refine_no_check
      ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true) ?with_ho
      ?(flags=dft ()) ?origsigma ?strict clenv =
  let open Proofview.Notations in
  let flags = Unification.flags_of flags in
  Proofview.tclEVARMAP >>= fun sigma ->
  clenv_refine_gen ~with_evars ~with_classes ~shelve_subgoals ?with_ho ?origsigma ?strict
                   flags (sigma, clenv)

let clenv_refine2 ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true) ?with_ho
                  ?(flags=dft ()) ?origsigma clenv =
  let flags = Unification.flags_of flags in
  clenv_unify_concl_tac flags clenv
   (clenv_refine_gen ~with_evars ~with_classes ~shelve_subgoals ?with_ho ?origsigma flags)

let with_clause (c, t) kont =
  let open Proofview in
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let sigma, cl = make_clenv_from_env env sigma (c, t) in
  Unsafe.tclEVARS sigma <*> kont cl end
