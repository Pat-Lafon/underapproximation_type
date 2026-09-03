open Language

type backend_pieces = {
  ext : string;
  preamble_path : string option;
  (* The text between the header and the query: datatype decls, measures, axioms. *)
  render_section : (string * Nt.t prop) list -> string;
  query_decl : int -> Nt.t prop -> string;
}

let lean_section axioms =
  let proofs =
    axioms
    |> List.map (fun (name, prop) ->
           Printf.sprintf "theorem %s : %s := by\n  prove_axiom\n\n" name
             (layout_prop_to_lean prop))
    |> String.concat ""
  in
  let axioms_namespace =
    Printf.sprintf "namespace Axioms\n%s\n\n%send Axioms"
      (render_axioms_scaffolding ())
      proofs
  in
  String.concat "\n\n"
    [ render_datatype_decls (); render_all_lean (); axioms_namespace ]
  ^ "\nopen Axioms\n"

let coq_section axioms =
  let rendered =
    List.map (fun (name, prop) -> (name, layout_prop_to_coq prop)) axioms
  in
  let axiom_decls =
    rendered
    |> List.map (fun (name, p) -> Printf.sprintf "Axiom %s : %s.\n" name p)
    |> String.concat ""
  in
  let theorems =
    rendered
    |> List.map (fun (name, p) ->
           Printf.sprintf "Theorem %s : %s.\nProof. prove_axiom. Qed.\n" name p)
    |> String.concat ""
  in
  let arguments =
    Measure.unfold_hint_names ()
    |> List.map (Printf.sprintf "Arguments %s /.")
    |> String.concat "\n"
  in
  let module_type =
    Printf.sprintf "Module Type COVERAGE_AXIOMS.\n%s\n\n%sEnd COVERAGE_AXIOMS."
      (render_measure_params_coq ())
      axiom_decls
  in
  let model =
    Printf.sprintf "Module Model <: COVERAGE_AXIOMS.\n%s\n\n%s\n\n%sEnd Model."
      (render_all_coq ()) arguments theorems
  in
  String.concat "\n\n" [ render_datatype_decls_coq (); module_type; model ]
  ^ "\n"

let pieces = function
  | `Lean ->
      {
        ext = ".lean";
        preamble_path = TypecheckerConfig.get_lean_preamble_path ();
        render_section = lean_section;
        query_decl =
          (fun idx goal ->
            Printf.sprintf "\ntheorem subtyping_query_%i : %s := by\n  sorry\n"
              idx (layout_prop_to_lean goal));
      }
  | `Coq ->
      {
        ext = ".v";
        preamble_path = TypecheckerConfig.get_coq_preamble_path ();
        render_section = coq_section;
        query_decl =
          (fun idx body ->
            Printf.sprintf
              "\n\
               Module Query (A : COVERAGE_AXIOMS).\n\
               Import A.\n\
               Lemma subtyping_query_%i : %s.\n\
               Proof.\n\
               Admitted.\n\
               End Query.\n"
              idx (layout_prop_to_coq body));
      }

let emit_axiom_preamble p oc axioms =
  let header =
    match p.preamble_path with
    | Some path -> In_channel.with_open_text path In_channel.input_all
    | None -> ""
  in
  [ header; p.render_section axioms ]
  |> List.filter (fun s -> String.length (String.trim s) > 0)
  |> String.concat "\n\n" |> output_string oc

let query_dir =
  lazy
    (let dir =
       Filename.concat
         (Filename.get_temp_dir_name ())
         "coverage_subtyping_queries"
     in
     (try Sys.mkdir dir 0o755 with Sys_error _ when Sys.file_exists dir -> ());
     dir)

let emit_query backend axioms query =
  let p = pieces backend in
  let idx = !Prover.query_counter in
  let filename =
    Filename.concat (Lazy.force query_dir)
      (Printf.sprintf "subtyping_query_%i%s" idx p.ext)
  in
  Out_channel.with_open_text filename (fun oc ->
      emit_axiom_preamble p oc axioms;
      output_string oc (p.query_decl idx query);
      ZUtilsLog.queries (fun () ->
          Printf.eprintf "Emitted subtyping query to %s\n" filename))
