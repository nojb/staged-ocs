(* Main program entry point.  *)

open Ocs_types
open Ocs_error

let main () = 
  let loadf = ref [] in
  let addf x = loadf := !loadf @ [x] in
  let argspec = [
    ("-dstaged", Arg.Set Ocs_top.dstaged, "Dump staged code in interactive mode");
    ("file", Arg.Rest addf, "Files to run in batch mode")
  ] in
    Arg.parse argspec addf (Printf.sprintf "Usage: %s [-dstaged] [ file ... ]" Sys.argv.(0));
    if !loadf = [] then
      Ocs_top.interactive ()
    else
      let e = Ocs_top.make_env ()
      and th = Ocs_top.make_thread () in
        try
          List.iter (fun x -> Ocs_prim.load_file e th x) !loadf
        with
          Error err ->
            Printf.eprintf "Error: %s\n" err
        | ErrorL ((file, line), err) ->
            Printf.eprintf "%s:%d: %s\n" file line err
;;

main ();;

