open Language

type backend_pieces = {
  preamble_path : string option;
  (* The text between the header and the query: datatype decls, measures, axioms. *)
  render_section : (string * Nt.t prop) list -> string;
}

let coq_section axioms =
  let rendered =
    List.map (fun (name, prop) -> (name, layout_prop_to_rocq prop)) axioms
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
  let module_type =
    Printf.sprintf "Module Type COVERAGE_AXIOMS.\n%s\n\n%sEnd COVERAGE_AXIOMS."
      (render_measure_params_coq ())
      axiom_decls
  in
  let model =
    Printf.sprintf "Module Model <: COVERAGE_AXIOMS.\n%s\n\n%s\n\n%sEnd Model."
      (render_all_coq ()) (render_arguments_coq ()) theorems
  in
  String.concat "\n\n" [ render_datatype_decls_coq (); module_type; model ]
  ^ "\n"

let pieces = function
  | `Coq ->
      {
        preamble_path = TypecheckerConfig.get_coq_preamble_path ();
        render_section = coq_section;
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
