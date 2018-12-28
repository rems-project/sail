default Order dec

val SignalException : unit -> unit effect {rreg}

val SignalExceptionBadAddr : unit -> unit effect {rreg}

function SignalExceptionBadAddr() = {
    SignalException();
}

struct CapStruct = {
    base : bool,
}

type CapReg = CapStruct

function getCapBase(c)   : CapStruct -> bool = c.base

register KCC : CapReg

function SignalException () = {
    base = getCapBase(KCC);
    ();
}

val "print_endline" : string -> unit

val main : unit -> unit

function main() = {
  print_endline("ok")
}