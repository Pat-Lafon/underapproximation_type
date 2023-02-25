open Json
open Yojson.Basic.Util
open Env

let load meta_fname fname =
  let metaj = load_json meta_fname in
  let j = load_json fname in
  let mode =
    match metaj |> member "mode" |> to_string with
    | "debug" ->
        let logfile = j |> member "logfile" |> to_string in
        Debug logfile
    | "release" -> Release
    | _ -> failwith "config: unknown mode"
  in
  let resfile = metaj |> member "resfile" |> to_string in
  let logfile = metaj |> member "logfile" |> to_string in
  let p = j |> member "prim_path" in
  let prim_path =
    {
      normalp = p |> member "normalp" |> to_string;
      overp = p |> member "overp" |> to_string;
      underp = p |> member "underp" |> to_string;
      rev_underp = p |> member "rev_underp" |> to_string;
      type_decls = p |> member "type_decls" |> to_string;
      lemmas = p |> member "lemmas" |> to_string;
      functional_lemmas = p |> member "functional_lemmas" |> to_string;
    }
  in
  let open Abstraction in
  let all_mps = j |> member "all_mps" |> to_list |> List.map to_string in
  let measure = j |> member "measure" |> to_string in
  let underr =
    match Inputstage.load_under_refinments prim_path.underp with
    | [], underr, [] -> underr
    | _, _, _ -> failwith "wrong under prim"
  in
  let rev_underr =
    match Inputstage.load_under_refinments prim_path.rev_underp with
    | [], underr, [] -> underr
    | _, _, _ -> failwith "wrong under prim"
  in
  let lemmas = Inputstage.load_lemmas prim_path.lemmas in
  let lemmas =
    List.filter (fun (_, lemma) -> Lemma.filter_by_mps all_mps lemma) lemmas
  in
  let functional_lemmas = Inputstage.load_lemmas prim_path.functional_lemmas in
  let functional_lemmas =
    List.filter
      (fun (_, lemma) -> Lemma.filter_by_mps all_mps lemma)
      functional_lemmas
  in
  (* let () = failwith "end" in *)
  let () =
    Prim.init
      ( Inputstage.load_type_decls prim_path.type_decls,
        Inputstage.load_normal_refinements prim_path.normalp,
        (* Inputstage.load_over_refinments prim_path.overp, *)
        [],
        underr,
        rev_underr,
        lemmas,
        functional_lemmas )
  in
  config := Some { mode; logfile; resfile; all_mps; prim_path; measure }

let get_resfile () =
  match !config with
  | None -> failwith "get_resfile"
  | Some config -> config.resfile

let get_mps () =
  match !config with
  | None -> failwith "uninited prim path"
  | Some config -> config.all_mps

let get_prim_path () =
  match !config with
  | None -> failwith "uninited prim path"
  | Some config -> config.prim_path

let load_default () = load "meta-config.json" "config/config.json"

let%test_unit "load_default" =
  let () = Printf.printf "%s\n" (Sys.getcwd ()) in
  let () = load "../../../meta-config.json" "../../../config/config.json" in
  match !config with
  | None -> failwith "empty config"
  | Some config -> (
      match config.mode with
      | Debug ".log" -> ()
      | m ->
          failwith
          @@ Printf.sprintf "wrong mode: %s"
          @@ Sexplib.Sexp.to_string @@ sexp_of_mode m)
