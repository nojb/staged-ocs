(* Main types used *)

open Ocs_vartable

(* We have to declare most types here to avoid cross-dependencies between
   compilation units.  *)

type sval = 
  (* Global variables are set to Sunbound when referenced but not assigned.  *)
    Sunbound

  (* List terminator.  *)
  | Snull

  (* End-of-file indicator.  *)
  | Seof

  (* Boolean values.  This is more compact than Sbool of bool.  *)
  | Strue
  | Sfalse

  (* String object.  *)
  | Sstring of string

  (* Symbol type.  Symbols should not be created directly, but using
     Ocs_sym.get_symbol, which ensures that they are unique and can be
     compared using ==.  *)
  | Ssymbol of string

  (* Numeric types.  *)
  | Sint of int
  | Sreal of float
  | Scomplex of Complex.t
  | Sbigint of Big_int.big_int
  | Srational of Ratio.ratio

  (* Character.  *)
  | Schar of char

  (* A pair (list element).  *)
  | Spair of spair

  (* Vector.  *)
  | Svector of sval array

  (* Port object.  *)
  | Sport of Ocs_port.port

  (* A primitive.  *)
  | Sprim of sproc

  (* A closure created by combining the process reference with the
     local environment at that point of execution.  *)
  | Sproc of sproc

  (* Delayed expression.  *)
  | Spromise of sval Lazy.t

  (* A set of values returned by the 'values' primitive,
     deconstructed into multiple parameters by call-with-values.  *)
  | Svalues of sval list

  (* A symbol explicitly tied to an environment that defines its scope.
     These symbols are generated by macro expansions and eliminated
     prior to evaluation.  *)
  | Sesym of env * sval

  (* Wrapped values are stub functions that encapsulate external values
     of unknown types.  *)
  | Swrapped of (unit -> unit)

  (* An unspecified value.  *)
  | Sunspec

  (* The actual type of a pair (cons cell).  *)
and spair =
  {
    mutable car : sval;
    mutable cdr : sval
  }

and _ ret =
    Rval : sval ret
  | Rcont : (thread -> sval) ret

  (* Primitive signature.  *)
and _ sg =
    Pfix : 'b sg -> (sval -> 'b) sg
  | Prest : 'b ret -> (sval list -> 'b) sg
  | Pret : 'a ret -> 'a sg
  | Pvoid : 'a ret -> (unit -> 'a) sg

  (* Procedure structure.  *)
and sproc =
  {
    proc_name : string;
    proc_fun : procf
  }

and procf =
    Pf : 'a sg * 'a -> procf

  (* Code types are used to represent analyzed expressions prepared for
     evaluation.  *)
and scode =
    Cval of sval
  | Cseq of scode list
  | Cand of scode list
  | Cor of scode list
  | Cif of scode * scode * scode
  | Csetg of gvar * scode
  | Csetl of int * scode
  | Cdefine of gvar * scode
  | Cgetg of gvar
  | Cgetl of int
  | Capply of scode * scode list
  | Clambda of slambda
  | Cqqp of scode * scode
  | Cqqv of scode list
  | Cqqvs of scode list
  | Cqqspl of scode
  | Ccond of (scode * scode) list
  | Ccondspec of scode
  | Ccase of scode * (sval list * scode) list
  | Cdelay of scode

and slambda =
  {
    lam_body : scode;
    lam_args : vbind list;
    lam_has_rest : bool;
    lam_name : string option
  }

  (* Global variable slot.  *)
and gvar =
  {
    mutable g_sym : sval;
    mutable g_val : sval
  }

  (* Thread state, used during evaluation.  *)
and thread =
  {
    th_stdin : sval;			(* Default input port.  *)
    th_stdout : sval;			(* Default output port.  *)
    th_dynext : dynext option		(* Current dynamic extent.  *)
  }

  (* Local variable slot. *)
and vloc =
  {
    mutable l_mut : bool;   (* Whether the variable is mutated. *)
    l_pos : int             (* Frame index *)
  }

  (* Bindings, used during analysis.  *)
and vbind =
    Vglob of gvar
  | Vloc of vloc
  | Vsyntax of (env -> sval list -> scode)
  | Vmacro of (env -> sval array -> sval)
  | Vkeyword of string

  (* Environment, used during analysis.  *)
and env =
  {
    env_depth : int;
    env_vartable : vbind vartable;
    env_frame_size : int ref;
    mutable env_tagged : (env * sval * vbind) list
  }

  (* Dynamic extents are associated with threads and continuations.  *)
and dynext =
  {
    dynext_parent : dynext option;
    dynext_depth : int;
    dynext_before : thread * ((sval -> unit) -> unit);
    dynext_after : thread * ((sval -> unit) -> unit)
  }

