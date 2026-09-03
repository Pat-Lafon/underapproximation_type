open Zutils
open Prop
open Sugar
open Measure

let layout_prop_to_coq = layout_prop_ coqsetting

(* Constructor names arrive lowercased; the rendered [Inductive] and its [match] arms
   use the capitalized form ([Nil]/[Cons]). *)
let coq_ctor (cname : string) = String.capitalize_ascii cname

let render_inductive_coq (d : Z3decls.datatype_decl) : string =
  spf "Inductive %s : Type :=\n%s." d.dt_name
    (List.map
       (Export_helper.ctor_line ~layout_ty:coq_layout_ty ~ctor:coq_ctor)
       d.ctors
    |> String.concat "\n")

(* The recognizer/accessor function names ([is_nil]/[tail]) are lowercase to match
   the relational predicate names the axioms reference. *)
let render_match_def_coq (d : Z3decls.datatype_decl) ~name ~ret
    (arm : Z3decls.ctor_spec -> string) : string =
  spf
    "Definition %s (x : %s) : %s :=\n\
    \  match x with\n\
     %s\n\
    \  end.\n\
     #[local] Hint Unfold %s : axunfold."
    name d.dt_name ret
    (List.map arm d.ctors |> String.concat "\n")
    name

let render_recognizer_coq (d : Z3decls.datatype_decl)
    (target : Z3decls.ctor_spec) : string =
  render_match_def_coq d
    ~name:(spf "is_%s" (String.lowercase_ascii target.cname))
    ~ret:"bool"
    (fun c ->
      let rhs = if c.cname = target.cname then "true" else "false" in
      spf "  | %s%s => %s" (coq_ctor c.cname) (Export_helper.wildcards c) rhs)

let render_accessor_coq (d : Z3decls.datatype_decl) (f : Z3decls.field_spec) :
    string =
  render_match_def_coq d ~name:f.fname
    ~ret:(spf "option %s" (coq_layout_ty f.ftype))
    (fun c ->
      if Export_helper.ctor_has_field f c then
        spf "  | %s %s => Some %s" (coq_ctor c.cname)
          (Export_helper.accessor_binders f c)
          (Export_helper.binder_of f)
      else spf "  | %s%s => None" (coq_ctor c.cname) (Export_helper.wildcards c))

(* Accessors return [option T] (above), yet a comparison can pit a bare [T]
   against that result; Coq won't type it without this [T >-> option] coercion.
   [Arguments _ /.] makes [cbn] unfold the inserted [some_<dt> xs] back to
   [Some xs], so [prove_axiom]'s [injection] can strip the constructor. *)
let render_option_coercion_coq (d : Z3decls.datatype_decl) : string =
  spf
    "Definition some_%s (x : %s) : option %s := Some x.\n\
     Coercion some_%s : %s >-> option.\n\
     Arguments some_%s /."
    d.dt_name d.dt_name d.dt_name d.dt_name d.dt_name d.dt_name

(* Reuses [Export_helper.accessor_fields] so both backends order accessors identically. *)
let render_datatype_decl_coq (d : Z3decls.datatype_decl) : string =
  let recognizers = List.map (render_recognizer_coq d) d.ctors in
  let accessors =
    List.map (render_accessor_coq d) (Export_helper.accessor_fields d)
  in
  String.concat "\n\n"
    ((render_inductive_coq d :: render_option_coercion_coq d :: recognizers)
    @ accessors)

let render_datatype_decls_coq () : string =
  Z3decls.registered_decls ()
  |> List.map render_datatype_decl_coq
  |> String.concat "\n\n"

open Ast

(* Primop in term position: Coq's [Z_scope] [<]/[>]/… are [Prop]-valued, so each
   renders as its [Z] boolean test [<?]/[>?]/…. Equality routes through the [eq]
   field of [coq_term_setting] instead. *)
let coq_primop = function
  | ">" -> ">?"
  | "<" -> "<?"
  | ">=" -> ">=?"
  | "<=" -> "<=?"
  | ("+" | "-" | "*" | "mod" | "&&" | "||") as p -> p
  | p -> _die_with [%here] (spf "coq_primop: unsupported primop %s" p)

let coq_term_setting : Export_helper.term_setting =
  {
    ctor_ref = coq_ctor;
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
  }

let render_rt_coq = Export_helper.render_rt_ coq_term_setting

let render_def ~kw =
  Export_helper.render_def ~kw ~stmt_end:"."
    ~layout_typedid:coqsetting.layout_typedid

(* A [Fixpoint] with no recursive call fails Coq's termination check, so a non-recursive
   measure must render as [Definition]. *)
let render_function_def_coq ~(recursive : bool) ~(name : string)
    ~(params : (Nt.t, string) typed list) ~(body : (Nt.t, Nt.t raw_term) typed)
    : string =
  render_def
    ~kw:(if recursive then "Fixpoint" else "Definition")
    ~name ~params ~retty:(coq_layout_ty body.ty) ~body:(render_rt_coq body)

(* Twin of [render_wrapper_def]: the body is propositional [impl args = res], not the
   boolean equality used inside measure bodies. *)
let render_wrapper_def_coq ~(base : string) ~(impl : string)
    ~(params : (Nt.t, string) typed list) ~(ret : Nt.t) : string =
  let call = String.concat " " (impl :: List.map (fun p -> p.x) params) in
  render_def ~kw:"Definition" ~name:base
    ~params:(params @ [ "res"#:ret ])
    ~retty:"Prop" ~body:(spf "%s = res" call)

(* Abstract relational symbol for the [Module Type] interface: the wrapper's signature
   with no body, so a query importing the interface can't unfold it. Twin of the concrete
   [render_wrapper_def_coq], which lands inside [Model] instead. *)
let render_measure_param_coq ~(base : string)
    ~(params : (Nt.t, string) typed list) ~(ret : Nt.t) : string =
  let arrows =
    List.map (fun p -> coq_layout_ty p.ty) params
    @ [ coq_layout_ty ret; "Prop" ]
  in
  spf "Parameter %s : %s." base (String.concat " -> " arrows)

(* The [export-axioms-coq] output is coqc-checked per benchmark, covering the arms they
   reach. These pin what no benchmark reaches, so coqc never sees: the bool [==] to
   [Bool.eqb] / [!=] to
   [negb] dispatch (reachable via a measure's [<>] or bool [=] — to_raw_term's
   [normalize_eq_op]), and the [Fixpoint] half of the [is_self_recursive] split. *)
let%test_module "coq term and measure rendering" =
  (module struct
    let ic n = Nt.Ty_constructor (n, [])
    let param name ty : (Nt.t, string) typed = { ty; x = name }

    let var name ty : (Nt.t, Nt.t raw_term) typed =
      { ty; x = Var { ty; x = name } }

    let lit ty c : (Nt.t, Nt.t raw_term) typed = { ty; x = Const c }

    let len_body : (Nt.t, Nt.t raw_term) typed =
      let succ_call : (Nt.t, Nt.t raw_term) typed =
        {
          ty = ic "int";
          x =
            AppOp
              ( { ty = ic "int"; x = PrimOp "+" },
                [
                  lit (ic "int") (I 1);
                  {
                    ty = ic "int";
                    x = App (var "len_impl" (ic "int"), [ var "t" (ic "ilist") ]);
                  };
                ] );
        }
      in
      {
        ty = ic "int";
        x =
          Match
            {
              matched = var "l" (ic "ilist");
              match_cases =
                [
                  Matchcase
                    {
                      constructor = param "nil" (ic "ilist");
                      args = [];
                      exp = lit (ic "int") (I 0);
                    };
                  Matchcase
                    {
                      constructor = param "cons" (ic "ilist");
                      args = [ param "_" (ic "int"); param "t" (ic "ilist") ];
                      exp = succ_call;
                    };
                ];
            };
      }

    let eq (op : string) a b : (Nt.t, Nt.t raw_term) typed =
      {
        ty = ic "bool";
        x = AppOp ({ ty = ic "bool"; x = PrimOp op }, [ a; b ]);
      }

    let eq_demo_body : (Nt.t, Nt.t raw_term) typed =
      {
        ty = ic "bool";
        x =
          Ifte
            ( eq "==" (var "x" (ic "int")) (lit (ic "int") (I 0)),
              eq "==" (var "b" (ic "bool")) (lit (ic "bool") (B true)),
              eq "!=" (var "x" (ic "int")) (lit (ic "int") (I 0)) );
      }

    let%test "self-recursive measure renders Fixpoint" =
      String.equal
        (render_function_def_coq ~recursive:true ~name:"len_impl"
           ~params:[ param "l" (ic "ilist") ]
           ~body:len_body)
        {|Fixpoint len_impl (l : ilist) : Z :=
  match l with
  | Nil => 0
  | Cons _ t => 1 + (len_impl t)
  end.|}

    let%test "equality dispatches on operand sort" =
      String.equal
        (render_function_def_coq ~recursive:false ~name:"eq_demo_impl"
           ~params:[ param "x" (ic "int"); param "b" (ic "bool") ]
           ~body:eq_demo_body)
        {|Definition eq_demo_impl (x : Z) (b : bool) : bool :=
  if x =? 0 then Bool.eqb b true else negb (x =? 0).|}
  end)

(* Coq twin of [Lean_export.render_all_lean]. *)
let render_all_coq : unit -> string =
  render_impl_wrapper
    ~impl:(fun (d : rec_def) ->
      render_function_def_coq ~recursive:(is_self_recursive d)
        ~name:(impl_name d.fname) ~params:d.params ~body:(to_impl_calls d.body))
    ~wrapper:(fun (d : rec_def) ->
      render_wrapper_def_coq ~base:d.fname ~impl:(impl_name d.fname)
        ~params:d.params ~ret:d.body.ty)

(* One abstract [Parameter] per measure — the module-type counterpart to [render_all_coq]'s
   concrete defs; [emit.ml] wraps this as [COVERAGE_AXIOMS] and that as [Model]. *)
let render_measure_params_coq : unit -> string =
  render_all (fun (d : rec_def) ->
      render_measure_param_coq ~base:d.fname ~params:d.params ~ret:d.body.ty)
