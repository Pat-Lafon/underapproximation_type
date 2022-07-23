open Zzdatatype.Datatype

let pretty_layout f ctx =
  List.split_by "; " (fun (name, ty) -> Printf.sprintf "%s:%s" name (f ty)) ctx

let pretty_layout_judge f ctx (e, r) =
  Printf.sprintf "%s⊢\n%s :\n%s\n" (pretty_layout f ctx) (Expr.layout e) (f r)

let pretty_layout_over_judge f ctx (e, r) =
  pretty_layout_judge Overtype.pretty_layout ctx
    (Languages.Termlang.erase_type @@ f e, r)

let pretty_layout_under_judge f ctx (e, r) =
  pretty_layout_judge Undertype.pretty_layout ctx
    (Languages.Termlang.erase_type @@ f e, r)

let pretty_layout_subtyping f ctx (r1, r2) =
  Printf.sprintf "%s⊢\n%s <:\n%s\n" (pretty_layout f ctx) (f r1) (f r2)

let pretty_layout_over_subtyping ctx (r1, r2) =
  pretty_layout_subtyping Overtype.pretty_layout ctx (r1, r2)

let pretty_layout_under_subtyping ctx (r1, r2) =
  pretty_layout_subtyping Undertype.pretty_layout ctx (r1, r2)
