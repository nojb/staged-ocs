(* Miscellaneous utility functions *)

open Ocs_types

val list_to_caml : sval -> sval list

val make_slist : sval -> sval list -> sval

val mkapply : scode -> scode array -> scode

val test_eqv : sval -> sval -> bool
val test_equal : sval -> sval -> bool
