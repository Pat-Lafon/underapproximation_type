open Language
open Zutils

let counter = ref 0

let lean_preamble =
  lazy
    (let preamble_path = Myconfig.get_lean_preamble_path () in
     try
       let ic = open_in preamble_path in
       Fun.protect
         ~finally:(fun () -> close_in ic)
         (fun () ->
           let n = in_channel_length ic in
           let s = Bytes.create n in
           really_input ic s 0 n;
           Bytes.to_string s)
     with exn ->
       failwith
         (Printf.sprintf "Could not read lean preamble at '%s': %s" preamble_path
            (Printexc.to_string exn)))

let dump_failed_query axioms query =
  let idx = !counter in
  counter := idx + 1;
  let filename =
    Filename.concat
      (Filename.get_temp_dir_name ())
      (Printf.sprintf "subtyping_failed_%i.lean" idx)
  in
  let oc =
    try open_out filename
    with exn ->
      failwith
        (Printf.sprintf "Could not open lean dump file '%s': %s" filename
           (Printexc.to_string exn))
  in
  Fun.protect
    ~finally:(fun () -> close_out oc)
    (fun () ->
      Printf.fprintf oc "-- Failed subtyping query #%i\n" idx;
      Printf.fprintf oc
        "-- To debug: prove or find a counterexample for the theorem below.\n";
      Printf.fprintf oc
        "-- The axioms are assumptions from the coverage type system.\n\n";
      (* Preamble ends with `namespace Axioms` + local attributes; close it
         after the axioms and `open Axioms` at top level so bare `apply ax_0`
         / `have := ax_5 …` still resolve in the `failed_subtyping_*` body. *)
      Printf.fprintf oc "%s" (Lazy.force lean_preamble);
      List.iteri
        (fun i ax ->
          Printf.fprintf oc "theorem ax_%i : %s := by\n  prove_axiom\n\n" i
            (layout_prop_to_lean ax))
        axioms;
      Printf.fprintf oc "end Axioms\n";
      Printf.fprintf oc "open Axioms\n";
      Printf.fprintf oc "\ntheorem failed_subtyping_%i : %s := by\n  sorry\n"
        idx (layout_prop_to_lean query));
  Printf.eprintf "Dumped failed subtyping query to %s\n" filename
