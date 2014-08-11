(* I/O primitives.  *)

open Ocs_types
open Ocs_error
open Ocs_env
open Ocs_prim
open Ocs_print
open Ocs_sym

let current_input_port =
  new_param (Sport (Ocs_port.input_port stdin)) (fun x -> x)
;;

let current_output_port =
  new_param (Sport (Ocs_port.output_port stdout)) (fun x -> x)
;;

let get_stdin () =
  match get_param current_input_port with
    Sport p -> p
  | _ ->
      raise (Error "current-input-port: not a port")
;;

let get_stdout () =
  match get_param current_output_port with
    Sport p -> p
  | _ ->
      raise (Error "current-output-port: not a port")
;;

let read =
  function
    [] ->
      Ocs_read.read_from_port (get_stdin ())
  | [ Sport port ] -> Ocs_read.read_from_port port
  | _ -> raise (Error "read: bad args")
;;

let rdchr p =
  match Ocs_port.getc p with
    Some c -> Schar c
  | None -> Seof
;;

let read_char =
  function
    [ ] -> rdchr (get_stdin ())
  | [ Sport port ] -> rdchr port
  | _ -> raise (Error "read-char: bad args")
;;

let peekchr p =
  match Ocs_port.getc p with
    Some c ->
      Ocs_port.ungetc p c;
      Schar c
  | None -> Seof
;;

let peek_char =
  function
    [ ] -> peekchr (get_stdin ())
  | [ Sport port ] -> peekchr port
  | _ -> raise (Error "peek-char: bad args")
;;

let eof_object =
  function
    Seof -> Strue
  | _ -> Sfalse
;;

let chrdy p =
  if Ocs_port.char_ready p then Strue else Sfalse
;;

let char_ready =
  function
    [ ] -> chrdy (get_stdin ())
  | [ Sport port ] -> chrdy port
  | _ -> raise (Error "char-ready?: bad args")
;;

let display =
  function
    [ obj ] ->
      let p = get_stdout () in print p true obj; Ocs_port.flush p; Sunspec
  | [ obj; Sport p ] -> print p true obj; Ocs_port.flush p; Sunspec
  | _ -> raise (Error "display: bad args")
;;

let write =
  function
    [ obj ] ->
      let p = get_stdout () in print p false obj; Ocs_port.flush p; Sunspec
  | [ obj; Sport p ] -> print p false obj; Ocs_port.flush p; Sunspec
  | _ -> raise (Error "write: bad args")
;;

let write_char =
  function
    [ Schar c ] ->
      let p = get_stdout () in Ocs_port.putc p c; Ocs_port.flush p; Sunspec
  | [ Schar c; Sport p ] -> Ocs_port.putc p c; Ocs_port.flush p; Sunspec
  | _ -> raise (Error "write-char: bad args")
;;

let newline =
  function
    [ ] ->
      let p = get_stdout () in Ocs_port.putc p '\n'; Ocs_port.flush p; Sunspec
  | [ Sport p ] -> Ocs_port.putc p '\n'; Ocs_port.flush p; Sunspec
  | _ -> raise (Error "newline: bad args")
;;

let is_input =
  function
    Sport p -> if Ocs_port.is_input p then Strue else Sfalse
  | _ -> Sfalse
;;

let is_output =
  function
    Sport p -> if Ocs_port.is_output p then Strue else Sfalse
  | _ -> Sfalse
;;

let open_input_file =
  function
    Sstring s -> Sport (Ocs_port.open_input_port s)
  | _ -> raise (Error "expected string as input file name")
;;

let open_output_file =
  function
    Sstring s -> Sport (Ocs_port.open_output_port s)
  | _ -> raise (Error "expected string as output file name")
;;

let close_port =
  function
    Sport p -> Ocs_port.close p
  | _ -> raise (Error "close-port: invalid argument")
;;

let scm_close_port p =
  close_port p; Sunspec
;;

(* Note that the call-with-*-file functions close the port if the
   procedure exits, so they must not be re-called using a captured
   continuation after they exit once.  Dynamic extents can't be used
   for this because closing and reopening the file would be an even
   bigger problem.  *)

let call_w_in name proc th =
  let p = open_input_file name in
  let x = apply th proc [p] in
    close_port p;
    x
;;

let call_w_out name proc th =
  let p = open_output_file name in
  let x = apply th proc [p] in
    close_port p;
    x
;;

let w_in name thunk th =
  let p = open_input_file name in
    let_param current_input_port p
      (fun () ->
         let x = apply th thunk [] in
           close_port p; x)
;;

let w_out name thunk th =
  let p = open_output_file name in
    let_param current_output_port p
      (fun () ->
         let x = apply th thunk [] in
           close_port p; x)
;;

let init e =
  set_pfn e read "read";
  set_pfn e read_char "read-char";
  set_pfn e peek_char "peek-char";
  set_pfn e char_ready "char-ready?";

  set_pf1 e eof_object "eof-object?";

  set_pfn e display "display";
  set_pfn e newline "newline";
  set_pfn e write "write";
  set_pfn e write_char "write-char";

  set_glob e sym_current_input_port current_input_port;
  set_glob e sym_current_output_port current_output_port;

  set_pf1 e is_input "input-port?";
  set_pf1 e is_output "output-port?";

  set_pf1 e open_input_file "open-input-file";
  set_pf1 e open_output_file "open-output-file";

  set_pf1 e scm_close_port "close-input-port";
  set_pf1 e scm_close_port "close-output-port";

  set_pfg e (Pfix (Pfix (Pret Rcont))) call_w_in "call-with-input-file";
  set_pfg e (Pfix (Pfix (Pret Rcont))) call_w_out "call-with-output-file";

  set_pfg e (Pfix (Pfix (Pret Rcont))) w_in "with-input-from-file";
  set_pfg e (Pfix (Pfix (Pret Rcont))) w_out "with-output-to-file";
;;
