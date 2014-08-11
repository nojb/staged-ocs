(** Implementation of dynamically scoped variables in Ocaml:
    delimited dynamic binding.

    We're using the CC (aka caml-shift) framework of multi-prompt
    delimited-continuation operators.

   Joint work with Chung-chieh Shan and Amr Sabry.

   $Id: dynvar.ml,v 1.1 2006/04/10 02:25:32 oleg Exp $
*)

(* We need the caml-shift library Delimcc:
   http://pobox.com/~oleg/ftp/continuations/implementations.html#caml-shift
*)

open Delimcc

(* First we define multi-prompt shift and abort. The latter is a convenient
   abbreviation 
   The operators below are _not_ trampolined ones!
*)

let shift p f = take_subcont p (fun sk () ->
  push_prompt p (fun () -> (f (fun v -> 
    push_prompt p (fun () -> push_subcont sk (fun () -> v))))))

let abort p v = take_subcont p (fun _ () -> v)


(* The function that never returns, and whose type is, therefore, 'a->'b *)
let ign x = failwith "cannot happen"


(* The implementation of the Dynvar interface *)

type 'a dynvar = ('a -> 'a) Delimcc.prompt

let dnew () = new_prompt ()

let dref p      = shift p (fun f -> fun v -> f v v)

let dset p newv = shift p (fun f -> fun v -> f v newv)

let dupp p g    = shift p (fun f -> fun y -> f (g y) y)

let dlet p v body = 
    let q = new_prompt () in
    push_prompt q (fun () ->
      ign 
       ((push_prompt p (fun () -> abort q (body ())))
	v))


