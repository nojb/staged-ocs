(* Top level, create and initialize the environment.  *)

open Ocs_types
open Ocs_error
open Ocs_env
open Ocs_compile
open Ocs_stage
open Ocs_print
open Ocs_macro

let dstaged = ref false

(* Create a top-level environment and bind standard primitives.  *)
let make_env () =
  let e = top_env () in
    bind_lang e;
    bind_macro e;
    Ocs_num.init e;
    Ocs_numstr.init e;
    Ocs_prim.init e;
    Ocs_vector.init e;
    Ocs_list.init e;
    Ocs_char.init e;
    Ocs_string.init e;
    Ocs_contin.init e;
    Ocs_io.init e;
    e
;;

(* Create a top-level thread.  *)
let make_thread () =
  { th_stdin = Sport (Ocs_port.input_port stdin);
    th_stdout = Sport (Ocs_port.output_port stdout);
    th_dynext = None }
;;

let get_port =
  function
    Sport p -> p
  | _ -> failwith "expected port"
;;

let top_loop env th =
  let inp = get_port th.th_stdin
  and outp = get_port th.th_stdout
  and errp = Ocs_port.output_port stderr in
  let lex = Ocs_lex.make_lexer inp "" in
    let rec loop () =
      Ocs_port.puts outp "> ";
      Ocs_port.flush outp;
      try
        match Ocs_read.read_expr lex with
          Seof -> ()
        | v ->
            let c = compile env v in
            let cv = stage .< th >. (fun v ->
                .< match .~v with
                     Sunspec -> ()
                   | r ->
                       print outp false r;
                       Ocs_port.putc outp '\n' >.) c in
              if !dstaged then
                begin
                  Print_code.print_code Format.str_formatter cv;
                  Ocs_port.puts errp (Format.flush_str_formatter ());
                  Ocs_port.flush errp
                end;
              Runcode.run cv;
              loop ()
      with Error err | ErrorL (_, err) ->
        Ocs_port.puts errp ("Error: " ^ err ^ "\n");
        Ocs_port.flush errp;
        loop ()
    in
      loop ()
;;

(* Simple interface to invoke the interactive Scheme environment.  *)
let interactive () =
  top_loop (make_env ()) (make_thread ())
;;

