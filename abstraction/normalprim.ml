open Zzdatatype.Datatype
module NT = Languages.Normalty

let tab =
  let open Languages.Normalty in
  [
    ("::", Ty_arrow (Ty_int, Ty_arrow (Ty_list Ty_int, Ty_list Ty_int)));
    ("[]", Ty_list Ty_int);
    ("<", Ty_arrow (Ty_int, Ty_arrow (Ty_int, Ty_bool)));
    (">", Ty_arrow (Ty_int, Ty_arrow (Ty_int, Ty_bool)));
    ("==", Ty_arrow (Ty_int, Ty_arrow (Ty_int, Ty_bool)));
    ("+", Ty_arrow (Ty_int, Ty_arrow (Ty_int, Ty_int)));
    ("-", Ty_arrow (Ty_int, Ty_arrow (Ty_int, Ty_int)));
  ]

(* let m = StrMap.from_kv_list tab *)

let m = ref None

let make_m under_m =
  m :=
    match !under_m with
    | None -> failwith "uninit under prim"
    | Some m -> Some (StrMap.map Languages.Underty.erase m)

(* let get_primitive_ty name = *)
(*   match !m with *)
(*   | None -> failwith "uninit normal prim" *)
(*   | Some m -> *)
(*       StrMap.find (Sugar.spf "cannot find primitive type of %s" name) m name *)
