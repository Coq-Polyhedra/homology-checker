let usage program =
  Printf.eprintf "Usage: %s CERTIFICATE.bin\n" program;
  2

let timed_check name check certificate =
  let started = Sys.time () in
  let result = check certificate in
  let elapsed = Sys.time () -. started in
  Printf.eprintf "%-24s %.6f s  %b\n%!" name elapsed result;
  result

let run filename =
  let started = Sys.time () in
  let certificate = Loader.load filename in
  let loaded = Sys.time () in
  Printf.eprintf "%-24s %.6f s\n%!" "certificate loading" (loaded -. started);
  let containment =
    timed_check "vertex containment"
      Extracted_checker.vertex_containment_check certificate
  in
  let equality =
    timed_check "vertex equality"
      Extracted_checker.vertex_equality_check certificate
  in
  let graph =
    timed_check "graph equality"
      Extracted_checker.graph_equality_check certificate
  in
  let accepted = containment && equality && graph in
  if accepted then 0 else 1

let () =
  let status =
    match Array.to_list Sys.argv with
    | [_; filename] ->
        (try run filename with
         | Loader.Malformed (offset, message) ->
             Printf.eprintf "Malformed certificate at byte %Ld: %s\n"
               offset message;
             2
         | Sys_error message ->
             Printf.eprintf "%s\n" message;
             2)
    | program :: _ -> usage program
    | [] -> usage "homology-checker"
  in
  exit status
