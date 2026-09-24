open Zutils
open Prop
open Sugar
open Measure

let rec lean_layout_ty = function
  | Nt.Ty_constructor (name, _) -> (
      match name with
      | "bool" -> "Bool"
      | "int" -> "Int"
      | "unit" -> "Unit"
      | _ -> name)
  | Nt.Ty_tuple tys -> String.concat " × " (List.map lean_layout_ty tys)
  | ty ->
      _die_with [%here]
        (spf "lean_layout_ty: unsupported type '%s'" (Nt.layout ty))

let leansetting =
  {
    sym_true = "True";
    sym_false = "False";
    sym_and = " ∧ ";
    sym_or = " ∨ ";
    sym_not = "¬";
    sym_implies = "→";
    sym_iff = "↔";
    sym_forall = "∀ ";
    sym_exists = "∃ ";
    layout_typedid = (fun x -> spf "(%s : %s)" x.x (lean_layout_ty x.ty));
    layout_mp = (function "==" -> "=" | "!=" -> "≠" | "mod" -> "%" | x -> x);
  }

let layout_prop_to_lean = layout_prop_with leansetting

let lean_primop = function
  | "mod" -> "%"
  | ("+" | "-" | "*" | ">" | "<" | ">=" | "<=" | "&&" | "||") as p -> p
  | p -> _die_with [%here] (spf "lean_primop: unsupported primop %s" p)

let lean_export_setting : Export_helper.setting =
  {
    ctor_ref = (fun c -> "." ^ Export_helper.ctor_name c);
    primop = lean_primop;
    not_ = (fun a -> spf "!%s" a);
    (* Term equality stays Bool-valued [==]/[!=] ([BEq]), unlike the propositional
       [=] that [layout_mp] emits for prop bodies. *)
    eq = (fun op lhs rhs _ -> spf "%s %s %s" lhs op rhs);
    match_end = "";
    let_sep = "";
    layout_ty = lean_layout_ty;
    option_ty = spf "Option %s";
    some_ = "some";
    none_ = "none";
    inductive =
      (fun d lines ->
        spf "inductive %s where\n%s\n  deriving DecidableEq, Repr" d.dt_name
          (String.concat "\n" lines));
    match_def =
      (fun d ~name ~ret arms ->
        spf "@[simp, grind =] def %s : %s → %s\n%s" name d.dt_name ret
          (String.concat "\n" arms));
    dt_extra = (fun _ -> []);
  }

let render_datatype_decls =
  Export_helper.render_datatype_decls lean_export_setting

(* These [@[simp, grind =]] defs, in [render_datatype_decl] emission order, are what
   [namespace Axioms] re-declares [local]. *)
let datatype_def_names () : string list =
  Z3decls.registered_decls ()
  |> List.concat_map (fun (d : Z3decls.datatype_decl) ->
         List.map Export_helper.recognizer_name d.ctors
         @ List.map
             (fun (f : Z3decls.field_spec) -> f.fname)
             (Export_helper.accessor_fields d))

(* The inductive type names (topo order), targets of [attribute [local grind cases]]. *)
let datatype_type_names () : string list =
  Z3decls.registered_decls ()
  |> List.map (fun (d : Z3decls.datatype_decl) -> d.dt_name)

open Ast

let render_rt = Export_helper.render_rt_ lean_export_setting

let render_def =
  Export_helper.render_def ~kw:"def" ~stmt_end:""
    ~layout_typedid:leansetting.layout_typedid

(* [params] carry the lambda binders; [body] is the function body proper, outer lambdas
   already stripped. *)
let render_function_def ~(name : string) ~(params : (Nt.t, string) typed list)
    ~(body : (Nt.t, Nt.t raw_term) typed) : string =
  render_def ~name ~params ~retty:(lean_layout_ty body.ty)
    ~body:(render_rt body)

(* The bridge lemma + [grind_pattern] for a measure. [rfl] closes
   it because the wrapper is definitionally [impl args = res]. *)
let render_intro_lemma ~(base : string) ~(impl : string)
    ~(params : (Nt.t, string) typed list) : string =
  let args = List.map (fun p -> p.x) params in
  let binders =
    String.concat " " (List.map leansetting.layout_typedid params)
  in
  let impl_call = String.concat " " (impl :: args) in
  let rel_app = String.concat " " ((base :: args) @ [ spf "(%s)" impl_call ]) in
  spf "  theorem %s_intro %s : %s := rfl\n  grind_pattern %s_intro => %s" base
    binders rel_app base impl_call

let render_all_lean : unit -> string =
  Export_helper.render_impl_wrapper
    ~impl:(fun (d : rec_def) ->
      render_function_def ~name:(impl_name d.fname) ~params:d.params
        ~body:(to_impl_calls d.body))
    ~wrapper:(Export_helper.render_wrapper ~render_def)

(* Heads the body of [namespace Axioms], ahead of the axiom theorems. Attributes are [local] so
   this simp/grind config stays scoped to those theorems — dropped at [end Axioms], not leaking
   into the rest of the file. *)
let render_axioms_scaffolding () : string =
  let attr modifiers names =
    spf "  attribute [%s] %s" modifiers (String.concat " " names)
  in
  let intros =
    Export_helper.render_all
      (fun (d : rec_def) ->
        render_intro_lemma ~base:d.fname ~impl:(impl_name d.fname)
          ~params:d.params)
      ()
  in
  String.concat "\n"
    [
      attr "local simp, local grind ="
        (datatype_def_names () @ unfold_hint_names ());
      attr "local grind cases" (datatype_type_names () @ [ "Bool" ]);
      "";
      intros;
    ]
