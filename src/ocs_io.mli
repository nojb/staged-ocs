(* I/O primitives *)

open Ocs_types
open Ocs_port

val current_input_port : sval
val current_output_port : sval

val get_stdin : unit -> port
val get_stdout : unit -> port

val read : sval list -> sval

val open_input_file : sval -> sval
val open_output_file : sval -> sval

val init : env -> unit

