open Language
open Zutils

let counter = ref 0

let lean_preamble =
  lazy
    (let preamble_path = Myconfig.get_lean_preamble_path () in
     In_channel.with_open_text preamble_path In_channel.input_all)

let dump_failed_query axioms query =
  let idx = !counter in
  counter := idx + 1;
  let filename =
    Filename.temp_file
      ~temp_dir:(Filename.get_temp_dir_name ())
      "subtyping_failed_" ".lean"
  in
  Out_channel.with_open_text filename (fun oc ->
      Printf.fprintf oc
        "-- Failed subtyping query #%i\n\
         -- To debug: prove or find a counterexample for the theorem below.\n\
         -- The axioms are assumptions from the coverage type system.\n\n"
        idx;
      (* Preamble ends with `namespace Axioms` + local attributes; close it
         after the axioms and `open Axioms` at top level so bare `apply ax_0`
         / `have := ax_5 …` still resolve in the `failed_subtyping_*` body. *)
      output_string oc (Lazy.force lean_preamble);
      List.iteri
        (fun i ax ->
          Printf.fprintf oc "theorem ax_%i : %s := by\n  prove_axiom\n\n" i
            (layout_prop_to_lean ax))
        axioms;
      output_string oc "end Axioms\nopen Axioms\n";
      Printf.fprintf oc "\ntheorem failed_subtyping_%i : %s := by\n  sorry\n"
        idx (layout_prop_to_lean query));
  Printf.eprintf "Dumped failed subtyping query to %s\n" filename
