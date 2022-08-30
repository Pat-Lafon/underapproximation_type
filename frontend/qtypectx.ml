open Quantified
open Languages.Qtypectx
open Zzdatatype.Datatype

let pretty_layout_raw (x : t) =
  Typectx.pretty_layout Underty.pretty_layout x.qbody

let pretty_layout (x : t) = layout_qt x.qvs [] (pretty_layout_raw x)

let pretty_print (x : t) =
  print_qt x.qvs [];
  Typectx.pretty_print Underty.pretty_layout x.qbody;
  print_newline ()

let pretty_layout_judge ctx (e, (r : Languages.Qunderty.t)) =
  Typectx.pretty_layout_judge (pretty_layout ctx) (e, Qunderty.pretty_layout r)

let pretty_print_judge ctx (e, (r : Languages.Underty.t)) =
  let () = Pp.printf "@{<bold>Type Check:@}\n" in
  pretty_print ctx;
  Pp.printf "⊢ @{<magenta>%s@} ⇦ " e;
  Pp.printf "@{<cyan>%s@}\n\n" @@ Underty.pretty_layout r

let pretty_print_app_judge ctx (args, (r : Languages.Underty.t)) =
  let () = Pp.printf "@{<bold>Application Type Check:@}\n" in
  pretty_print ctx;
  Pp.printf "⊢ @{<magenta>%s → ? @} ⇦ "
    (List.split_by " → " (fun x -> x.Languages.UnderAnormal.x) args);
  Pp.printf "@{<cyan>%s@}\n\n" @@ Underty.pretty_layout r

let pretty_print_infer ctx (e, (r : Languages.Underty.t)) =
  let () = Pp.printf "@{<bold>Type Infer:@}\n" in
  pretty_print ctx;
  Pp.printf "⊢ @{<magenta>%s@} ⇨ " e;
  Pp.printf "@{<cyan>%s@}\n\n" @@ Underty.pretty_layout r

let pretty_layout_subtyping ctx (r1, r2) =
  Typectx.pretty_layout_subtyping (pretty_layout ctx)
    (Qunderty.pretty_layout r1, Qunderty.pretty_layout r2)

let pretty_print_subtyping ctx (r1, r2) =
  let () = Pp.printf "@{<bold>Subtyping Check:@}\n" in
  pretty_print ctx;
  Pp.printf "⊢ @{<magenta>%s@} <: @{<cyan>%s@}\n\n" (Underty.pretty_layout r1)
    (Underty.pretty_layout r2)

(* let pretty_print_q uqvs eqvs pre (eq1, p1) (eq2, p2) = *)
(*   let () = Pp.printf "@{<bold>Query:@}\n" in *)
(*   Quantified.print_qt_ uqvs eqvs; *)
(*   Pp.printf "%s ⊨ @{<cyan>%s@} ==> @{<magenta>%s@}\n\n" *)
(*     (Autov.pretty_layout_prop pre) *)
(*     (Quantified.layout_qt_ [] eq2 (Autov.pretty_layout_prop p2)) *)
(*     (Quantified.layout_qt_ [] eq1 (Autov.pretty_layout_prop p1)) *)

let pretty_print_q uqvs eqvs prop =
  let () = Pp.printf "@{<bold>Query:@}\n" in
  Quantified.print_qt_ uqvs eqvs;
  Pp.printf "⊨ @{<cyan>%s@}\n\n" (Autov.pretty_layout_prop prop)
