open Zutils
open Prop
open Sugar
open Measure

(* Accessors return [option T], yet a comparison can pit a bare [T]
   against that result; Coq won't type it without this [T >-> option] coercion.
   [Arguments _ /.] makes [cbn] unfold the inserted [some_<dt> xs] back to
   [Some xs], so [prove_axiom]'s [injection] can strip the constructor. *)
let render_option_coercion_coq (d : Z3decls.datatype_decl) : string =
  spf
    "Definition some_%s (x : %s) : option %s := Some x.\n\
     Coercion some_%s : %s >-> option.\n\
     Arguments some_%s /."
    d.dt_name d.dt_name d.dt_name d.dt_name d.dt_name d.dt_name

open Ast

(* Primop in term position: Coq's [Z_scope] [<]/[>]/… are [Prop]-valued, so each
   renders as its [Z] boolean test [<?]/[>?]/…. Equality routes through the [eq]
   field of [coq_export_setting] instead. *)
let coq_primop = function
  | ">" -> ">?"
  | "<" -> "<?"
  | ">=" -> ">=?"
  | "<=" -> "<=?"
  | ("+" | "-" | "*" | "mod" | "&&" | "||") as p -> p
  | p -> _die_with [%here] (spf "coq_primop: unsupported primop %s" p)

let coq_export_setting : Export_helper.setting =
  {
    ctor_ref = Export_helper.ctor_name;
    primop = coq_primop;
    not_ = (fun a -> spf "negb %s" a);
    (* [=?] is [Z.eqb] — wrong for bool operands, so dispatch on sort to [Bool.eqb]. *)
    eq =
      (fun op lhs rhs ty ->
        let eqb =
          match ty with
          | Nt.Ty_constructor ("int", []) -> spf "%s =? %s" lhs rhs
          | Nt.Ty_constructor ("bool", []) -> spf "Bool.eqb %s %s" lhs rhs
          | ty ->
              _die_with [%here]
                (spf "coq eq: equality on unsupported type '%s'" (Nt.layout ty))
        in
        match op with "==" -> eqb | _ -> spf "negb (%s)" eqb);
    match_end = "\nend";
    let_sep = " in";
    layout_ty = rocq_layout_ty;
    option_ty = spf "option %s";
    some_ = "Some";
    none_ = "None";
    inductive =
      (fun d lines ->
        spf "Inductive %s : Type :=\n%s." d.dt_name (String.concat "\n" lines));
    match_def =
      (fun d ~name ~ret arms ->
        spf
          "Definition %s (x : %s) : %s :=\n\
          \  match x with\n\
           %s\n\
          \  end.\n\
           #[local] Hint Unfold %s : axunfold."
          name d.dt_name ret (String.concat "\n" arms) name);
    dt_extra = (fun d -> [ render_option_coercion_coq d ]);
  }

let render_datatype_decls_coq =
  Export_helper.render_datatype_decls coq_export_setting

let render_rt_coq = Export_helper.render_rt_ coq_export_setting

let render_def ~kw =
  Export_helper.render_def ~kw ~stmt_end:"."
    ~layout_typedid:rocqsetting.layout_typedid

(* A [Fixpoint] with no recursive call fails Coq's termination check, so a non-recursive
   measure must render as [Definition]. *)
let render_function_def_coq ~(recursive : bool) ~(name : string)
    ~(params : (Nt.t, string) typed list) ~(body : (Nt.t, Nt.t raw_term) typed)
    : string =
  render_def
    ~kw:(if recursive then "Fixpoint" else "Definition")
    ~name ~params ~retty:(rocq_layout_ty body.ty) ~body:(render_rt_coq body)

(* Abstract relational symbol for the [Module Type] interface: the wrapper's signature
   with no body, so a query importing the interface can't unfold it. The concrete
   wrapper lands inside [Model] instead. *)
let render_measure_param_coq ~(base : string)
    ~(params : (Nt.t, string) typed list) ~(ret : Nt.t) : string =
  let arrows =
    List.map (fun p -> rocq_layout_ty p.ty) params
    @ [ rocq_layout_ty ret; "Prop" ]
  in
  spf "Parameter %s : %s." base (String.concat " -> " arrows)

let render_all_coq : unit -> string =
  Export_helper.render_impl_wrapper
    ~impl:(fun (d : rec_def) ->
      render_function_def_coq ~recursive:(is_self_recursive d)
        ~name:(impl_name d.fname) ~params:d.params ~body:(to_impl_calls d.body))
    ~wrapper:
      (Export_helper.render_wrapper ~render_def:(render_def ~kw:"Definition"))

(* One abstract [Parameter] per measure — the module-type counterpart to [render_all_coq]'s
   concrete defs; [Emit] wraps this as [COVERAGE_AXIOMS] and that as [Model]. *)
let render_measure_params_coq : unit -> string =
  Export_helper.render_all (fun (d : rec_def) ->
      render_measure_param_coq ~base:d.fname ~params:d.params ~ret:d.body.ty)
