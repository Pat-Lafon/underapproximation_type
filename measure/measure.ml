open Zutils
open Prop
open Sugar
open Ast

(* A measure: an OCaml [let rec] method-predicate body registered from [program.ml].
   [fname] is the bare relational name [<p>]. *)
type rec_def = {
  fname : string;
  params : (Nt.t, string) typed list;
  body : (Nt.t, Nt.t raw_term) typed;
}

(* Measures, newest-registered first; [all_defs] reverses to source order. *)
let registry : (string * rec_def) list ref = ref []

let rec peel_lams acc (t : (Nt.t, Nt.t raw_term) typed) =
  match t.x with
  | Lam { lamarg; lambody } -> peel_lams (lamarg :: acc) lambody
  | _ -> (List.rev acc, t)

let impl_name (base : string) : string = base ^ "_impl"

(* Rename each measure reference [Var p] to [Var p_impl] so the encoded body calls its
   [define-fun-rec] impl. *)
let to_impl_calls (body : (Nt.t, Nt.t raw_term) typed) :
    (Nt.t, Nt.t raw_term) typed =
  List.fold_left
    (fun acc (name, _) ->
      typed_subst_raw_term name (fun v -> Var { v with x = impl_name v.x }) acc)
    body !registry

let register_items items : unit =
  List.iter
    (function
      | MFuncImpRaw { name; body; _ } ->
          if List.mem_assoc name.x !registry then
            _die_with [%here] (spf "duplicate method-predicate %s" name.x);
          let params, core = peel_lams [] body in
          if List.exists (fun p -> String.equal p.x "res") params then
            _die_with [%here]
              (spf
                 "measure %s has a parameter named \"res\", which collides \
                  with the wrapper result const"
                 name.x);
          registry :=
            (name.x, { fname = name.x; params; body = core }) :: !registry
      | _ -> ())
    items

let is_self_recursive (d : rec_def) : bool =
  List.exists (fun v -> String.equal v.x d.fname) (typed_fv_raw_term d.body)

(* The measure's base value, read off the body so nothing is hardcoded ([Leaf -> 5]
   yields 5): the integer its arm on the nullary constructor (the [Matchcase] with
   no argument binders) returns. The non-[Base] cases name why there is none. *)
type base_value = Base of int | No_nullary_arm | Non_literal_base

let base_value (d : rec_def) : base_value =
  match d.body.x with
  | Match { match_cases; _ } -> (
      match
        List.find_opt
          (function Matchcase { args; _ } -> args = [])
          match_cases
      with
      | Some (Matchcase { exp; _ }) -> (
          match exp.x with Const (I n) -> Base n | _ -> Non_literal_base)
      | None -> No_nullary_arm)
  | _ -> No_nullary_arm

let all_defs () : rec_def list = List.rev_map snd !registry

(* The measure def + wrapper names each proof backend marks unfoldable, to see through the
   functional encoding. *)
let unfold_hint_names () : string list =
  all_defs () |> List.concat_map (fun d -> [ d.fname; impl_name d.fname ])

let render_all (render_measure : rec_def -> string) () : string =
  all_defs () |> List.map render_measure |> String.concat "\n\n"

(* The impl+wrapper pair as text: one impl definition then its wrapper, per measure in source
   order. Each dialect supplies only the two per-measure renderers. *)
let render_impl_wrapper ~impl ~wrapper : unit -> string =
  render_all (fun (d : rec_def) -> impl d ^ "\n\n" ^ wrapper d)
