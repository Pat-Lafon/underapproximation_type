open Language
open FrontendTyped
open Sugar

type t = Nt.t

type feature_tab = t lit list
(** Features are list of boolean typed literals *)

type feature_vec = bool list
type feature_vec_id = int
type label = Pos | Neg | Unknown

let is_not_neg = function Neg -> false | _ -> true
let is_positive = function Pos -> true | _ -> false

(** feature vec and feature vec id is one-to-one correspondence *)

let feature_vec_to_id vec =
  let rec aux = function
    | [] -> 0
    | true :: vec -> 1 + (2 * aux vec)
    | false :: vec -> 0 + (2 * aux vec)
  in
  aux vec

let feature_id_to_vec (num_features : int) id =
  let rec aux (n, res) id =
    if n == num_features then
      if id == 0 then res else _failatwith __FILE__ __LINE__ "die"
    else aux (n + 1, (id mod 2 == 1) :: res) (id / 2)
  in
  aux (0, []) id


let feature_vec_to_prop (ftab : feature_tab) vec =
  let props =
    List.map (fun (b, lit) ->
        let lit = lit #: Nt.bool_ty in
        if b then Lit lit else Not (Lit lit))
    @@ List.combine vec ftab
  in
  match props with [] -> mk_true | _ -> And props

(* (\* HACK *\) *)
(* type stlc_cases = IsConst | IsVar | IsAbs | IsApp *)
(* let filter_conflict_vec (ftab : feature_tab) (vec : feature_vec) = *)
(*   let ass = List.combine ftab vec in *)
(*   let ass_num_app = *)
(*     List.filter *)
(*       (fun (lit, b) -> *)
(*         match lit with *)
(*         | AAppOp (op, _) when List.exists (String.equal op.x) stlc_list -> true *)
(*         | _ -> false) *)
(*       ass *)
(*   in *)
(*   let res = *)
(*   match ass_num_app with *)
(*   | [] -> true *)
(*   | (_, ass_num_app_b) :: _ -> *)
(*       let ass_4_cases = *)
(*         List.filter *)
(*           (fun (lit, b) -> *)
(*             match lit with *)
(*             | AAppOp (op, _) when List.exists (String.equal op.x) stlc_list -> b *)
(*             | _ -> false) *)
(*           ass *)
(*       in *)
(*       match ass_4_cases with *)
(*       | [(x, _)] -> *)
(*         let case = *)
(*         match x with *)
(*         | "is_const" -> IsConst *)
(*         | "is_var" -> IsVar *)
(*         | "is_abs" -> IsAbs *)
(*         | "is_app" -> IsApp *)
(*           | _ -> _failatwith __FILE__ __LINE__ "die" *)
(*       | _ -> false *)

(*       if List.length ass != 1 then ( *)
(*         Printf.printf "Filter out: %s\n" *)
(*           (layout_prop @@ feature_vec_to_prop ftab vec); *)
(*         false) *)
(*       else *)
(*         let case = match ass_4_cases with *)
(*           | [x] -> *)
(*         true *)

(* let filter_conflict_id (ftab : feature_tab) id = *)
(*   filter_conflict_vec ftab @@ feature_id_to_vec (List.length ftab) id *)

let feature_id_to_prop (ftab : feature_tab) id =
  feature_vec_to_prop ftab @@ feature_id_to_vec (List.length ftab) id

(** make features from template (universal quantified prop) *)

type template = { bvars : (t, string) typed list; body : t lit }

let is_guard_lit (lit : t lit) : (string * t) option =
  match lit with
  | AAppOp ({ x = name; _ }, [ { x = AVar w; _ } ])
    when String.starts_with ~prefix:"is_" name ->
      Some (w.x, w.ty)
  | _ -> None

let rec lit_v_under_non_builtin_appop v lit =
  match lit with
  | AC _ | AVar _ -> false
  | ATu ts -> List.exists (fun t -> lit_v_under_non_builtin_appop v t.x) ts
  | AProj (t, _) -> lit_v_under_non_builtin_appop v t.x
  | AAppOp (op, args) ->
      let here =
        (not (Op.is_builtin_op op.x))
        && List.exists
             (fun t ->
               match t.x with AVar w -> String.equal w.x v | _ -> false)
             args
      in
      here || List.exists (fun t -> lit_v_under_non_builtin_appop v t.x) args

let extract_atom = function
  | Lit l -> Some (false, l)
  | Not (Lit l) -> Some (true, l)
  | _ -> None

let mk_not_lit (l : (t, t lit) typed) : t lit =
  let op = "not" #: (Nt.construct_arr_tp ([ Nt.bool_ty ], Nt.bool_ty)) in
  AAppOp (op, [ l ])

let mk_and_lit (lits : (t, t lit) typed list) : t lit =
  let op =
    "&&" #: (Nt.construct_arr_tp ([ Nt.bool_ty; Nt.bool_ty ], Nt.bool_ty))
  in
  AAppOp (op, lits)

let prop_to_template prop =
  if fv_prop prop <> [] then _failatwith __FILE__ __LINE__ "die";
  let rec walk qvs_in_scope = function
    | Forall { qv; body } ->
        let qvs, body = walk (qv :: qvs_in_scope) body in
        (qv :: qvs, body)
    | Lit lit -> ([], lit.x)
    | And [ p1; p2 ] ->
        let atom_of p =
          match extract_atom p with
          | Some a -> a
          | None ->
              _failatwith __FILE__ __LINE__
                "template And: each conjunct must be Lit or Not Lit"
        in
        let a1 = atom_of p1 and a2 = atom_of p2 in
        let positive_guard (negated, l) =
          if negated then None else is_guard_lit l.x
        in
        let (v_name, v_ty), pred_atom =
          match (positive_guard a1, positive_guard a2) with
          | Some v, None -> (v, a2)
          | None, Some v -> (v, a1)
          | Some _, Some _ ->
              _failatwith __FILE__ __LINE__
                "template And: both conjuncts look like is_C(v) guards"
          | None, None ->
              _failatwith __FILE__ __LINE__
                "template And: no positive is_C(v) guard found"
        in
        let bound =
          List.exists
            (fun q -> String.equal q.x v_name && Nt.eq q.ty v_ty)
            qvs_in_scope
        in
        if not bound then
          _failatwith __FILE__ __LINE__
            "template And: guarded var is not a bound qvar of the matching type";
        let _, pred_lit = pred_atom in
        if not (lit_v_under_non_builtin_appop v_name pred_lit.x) then
          _failatwith __FILE__ __LINE__
            "template And: predicate doesn't reference guarded var under a \
             non-builtin AppOp";
        let to_typed (negated, l) =
          if negated then { l with x = mk_not_lit l } else l
        in
        ([], mk_and_lit [ to_typed a1; to_typed a2 ])
    | And _ ->
        _failatwith __FILE__ __LINE__
          "template And: exactly two conjuncts required (guard + predicate)"
    | _ -> _failatwith __FILE__ __LINE__ "unsupported template body shape"
  in
  let bvars, body = walk [] prop in
  { bvars; body }

open Zzdatatype.Datatype

let instantiate_template vars { bvars; body } =
  let vars_list =
    List.map (fun bvar -> List.filter (fun y -> Nt.eq bvar.ty y.ty) vars) bvars
  in
  let args_settings = List.choose_list_list vars_list in
  let args_settings = List.map (fun a -> List.combine bvars a) args_settings in
  let features =
    List.map
      (fun args_setting ->
        List.fold_right
          (fun (x, y) -> subst_lit_instance x.x (AVar y))
          args_setting body)
      args_settings
  in
  features

let name_to_avoid = [ "inv"; "mx"; "lo"; "hi" ]

let mk_features templates vars =
  let vars =
    List.filter
      (fun x -> List.for_all (fun y -> not (String.equal x.x y)) name_to_avoid)
      vars
  in
  let features =
    List.concat @@ List.map (instantiate_template vars) templates
  in
  let features =
    features
    @ List.filter_map
        (fun x -> match x.ty with Nt.Ty_bool -> Some (AVar x) | _ -> None)
        vars
  in
  let () =
    Env.show_debug_queries @@ fun _ ->
    Pp.printf "@{<bold>@{<orange>Features:@}@} %s\n"
      (List.split_by_comma layout_lit features)
  in
  (* let features = List.rev features in *)
  features

let templates : template list option ref = ref None

let init_template props =
  let ts = List.map prop_to_template props in
  templates := Some ts

let get_template () =
  match !templates with
  | None -> _failatwith __FILE__ __LINE__ "die"
  | Some ts -> ts

open Base

let ___check_vec_to_id (vec : feature_vec) =
  let vec' = feature_id_to_vec (List.length vec) (feature_vec_to_id vec) in
  List.equal Bool.equal vec vec'

let%test "vec_to_id1" = ___check_vec_to_id [ true; false; true ]
let%test "vec_to_id2" = Int.equal 1 @@ feature_vec_to_id [ true; false; false ]
let%test "vec_to_id3" = Int.equal 2 @@ feature_vec_to_id [ false; true; false ]
let%test "vec_to_id4" = Int.equal 5 @@ feature_vec_to_id [ true; false; true ]

module Test_prop_to_template = struct
  let irbtree_ty = Nt.Ty_constructor ("irbtree", [])

  let appop name arg_tys ret_ty args : (t, t lit) typed =
    let op = name #: Nt.(construct_arr_tp (arg_tys, ret_ty)) in
    (AAppOp (op, args)) #: ret_ty

  let avar name ty : (t, t lit) typed = (AVar (name #: ty)) #: ty
  let is_rbtnode v = appop "is_rbtnode" [ irbtree_ty ] Nt.bool_ty [ avar v irbtree_ty ]
  let color v = appop "color" [ irbtree_ty ] Nt.bool_ty [ avar v irbtree_ty ]
  let true_const = (AC (B true)) #: Nt.bool_ty

  let color_eq_true v =
    appop "==" [ Nt.bool_ty; Nt.bool_ty ] Nt.bool_ty [ color v; true_const ]

  let forall_v body : t prop = Forall { qv = "v" #: irbtree_ty; body }

  let is_failure f =
    match f () with _ -> false | exception Failure _ -> true

  let%test "single Lit accepts" =
    let body = Lit (is_rbtnode "v") in
    let t = prop_to_template (forall_v body) in
    match t.body with AAppOp ({ x = "is_rbtnode"; _ }, _) -> true | _ -> false

  let%test "single Lit accepts naked accessor (loose)" =
    let body = Lit (color_eq_true "v") in
    let t = prop_to_template (forall_v body) in
    match t.body with AAppOp ({ x = "=="; _ }, _) -> true | _ -> false

  let%test "guarded conjunction accepts" =
    let body = And [ Lit (is_rbtnode "v"); Lit (color_eq_true "v") ] in
    let t = prop_to_template (forall_v body) in
    match t.body with
    | AAppOp ({ x = "&&"; _ }, [ _; _ ]) -> true
    | _ -> false

  let%test "negated predicate accepts" =
    let body = And [ Lit (is_rbtnode "v"); Not (Lit (color_eq_true "v")) ] in
    let t = prop_to_template (forall_v body) in
    match t.body with
    | AAppOp ({ x = "&&"; _ }, [ _; _ ]) -> true
    | _ -> false

  let%test "three conjuncts rejects" =
    let body =
      And
        [
          Lit (is_rbtnode "v"); Lit (color_eq_true "v"); Lit (color_eq_true "v");
        ]
    in
    is_failure (fun () -> prop_to_template (forall_v body))

  let%test "no guard rejects" =
    let body = And [ Lit (color_eq_true "v"); Lit (color_eq_true "v") ] in
    is_failure (fun () -> prop_to_template (forall_v body))

  let%test "two guards rejects" =
    let body = And [ Lit (is_rbtnode "v"); Lit (is_rbtnode "v") ] in
    is_failure (fun () -> prop_to_template (forall_v body))

  let%test "predicate without non-builtin AppOp rejects" =
    let bare_eq =
      appop "==" [ irbtree_ty; irbtree_ty ] Nt.bool_ty
        [ avar "v" irbtree_ty; avar "v" irbtree_ty ]
    in
    let body = And [ Lit (is_rbtnode "v"); Lit bare_eq ] in
    is_failure (fun () -> prop_to_template (forall_v body))

  let%test "negated guard rejects" =
    let body = And [ Not (Lit (is_rbtnode "v")); Lit (color_eq_true "v") ] in
    is_failure (fun () -> prop_to_template (forall_v body))

  let%test "Or body rejects" =
    let body = Or [ Lit (is_rbtnode "v"); Lit (color_eq_true "v") ] in
    is_failure (fun () -> prop_to_template (forall_v body))

  let%test "Implies body rejects" =
    let body = Implies (Lit (is_rbtnode "v"), Lit (color_eq_true "v")) in
    is_failure (fun () -> prop_to_template (forall_v body))

  let%test "Not (And _) conjunct rejects" =
    let inner = And [ Lit (color_eq_true "v"); Lit (color_eq_true "v") ] in
    let body = And [ Lit (is_rbtnode "v"); Not inner ] in
    is_failure (fun () -> prop_to_template (forall_v body))
end
