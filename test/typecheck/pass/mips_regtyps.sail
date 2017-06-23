
(* mips_prelude.sail: declarations of mips registers, and functions common 
   to mips instructions (e.g. address translation) *)

(* bit vectors have indices decreasing from left i.e. msb is highest index *)
default Order dec

register (bit[64]) PC
register (bit[64]) nextPC

(* CP0 Registers *)

typedef CauseReg = register bits [ 31 : 0 ] {
  31       : BD; (* branch delay *)
  (*30       : Z0;*)
  29 .. 28 : CE; (* for coprocessor enable exception *)
  (*27 .. 24 : Z1;*)
  23       : IV; (* special interrupt vector not supported *)
  22       : WP; (* watchpoint exception occurred *)
  (*21 .. 16 : Z2; *)
  15 .. 8  : IP; (* interrupt pending bits *)
  (*7        : Z3;*)
  6 .. 2   : ExcCode; (* code of last exception *)
  (*1 .. 0   : Z4;*)
}

typedef TLBEntryLoReg = register bits [63 : 0] {
  63      : CapS;
  62      : CapL;
  29 .. 6 : PFN;
  5  .. 3 : C;
  2       : D;
  1       : V;
  0       : G;
}

typedef TLBEntryHiReg = register bits [63 : 0] {
  63 .. 62 : R;
  39 .. 13 : VPN2;
  7  ..  0 : ASID;
}

typedef ContextReg = register bits [63 : 0] {
  63 .. 23 : PTEBase;
  22 .. 4  : BadVPN2;
  (*3  .. 0  : ZR;*)
}

typedef XContextReg = register bits [63 : 0] {
  63 .. 33: PTEBase;
  32 .. 31: R;
  30 ..  4: BadVPN2;
}
