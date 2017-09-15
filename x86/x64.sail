(*========================================================================*)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(*========================================================================*)

default Order dec

val extern forall Type 'a. ('a, list<'a>) -> bool effect pure ismember
val extern forall Type 'a. list<'a> -> nat effect pure listlength

function (bit[8 ]) ASR8  ((bit[8 ]) v, ([|8 |]) shift) = let v2 = ((bit[16 ]) (EXTS(v))) in (bit[8 ]) (mask(v2 >> shift))
function (bit[16]) ASR16 ((bit[16]) v, ([|16|]) shift) = let v2 = ((bit[32 ]) (EXTS(v))) in (bit[16]) (mask(v2 >> shift))
function (bit[32]) ASR32 ((bit[32]) v, ([|32|]) shift) = let v2 = ((bit[64 ]) (EXTS(v))) in (bit[32]) (mask(v2 >> shift))
function (bit[64]) ASR64 ((bit[64]) v, ([|64|]) shift) = let v2 = ((bit[128]) (EXTS(v))) in (bit[64]) (mask(v2 >> shift))

function (bit[8 ]) ROR8  ((bit[8 ]) v, ([|8 |]) shift) = let v2 = ((bit[16 ]) (v:v)) in (bit[8 ]) (mask(v2 >> shift))
function (bit[16]) ROR16 ((bit[16]) v, ([|16|]) shift) = let v2 = ((bit[32 ]) (v:v)) in (bit[16]) (mask(v2 >> shift))
function (bit[32]) ROR32 ((bit[32]) v, ([|32|]) shift) = let v2 = ((bit[64 ]) (v:v)) in (bit[32]) (mask(v2 >> shift))
function (bit[64]) ROR64 ((bit[64]) v, ([|64|]) shift) = let v2 = ((bit[128]) (v:v)) in (bit[64]) (mask(v2 >> shift))

function (bit[8 ]) ROL8  ((bit[8 ]) v, ([|8 |]) shift) = let v2 = ((bit[16 ]) (v:v)) in (bit[8 ]) (mask(v2 << shift))
function (bit[16]) ROL16 ((bit[16]) v, ([|16|]) shift) = let v2 = ((bit[32 ]) (v:v)) in (bit[16]) (mask(v2 << shift))
function (bit[32]) ROL32 ((bit[32]) v, ([|32|]) shift) = let v2 = ((bit[64 ]) (v:v)) in (bit[32]) (mask(v2 << shift))
function (bit[64]) ROL64 ((bit[64]) v, ([|64|]) shift) = let v2 = ((bit[128]) (v:v)) in (bit[64]) (mask(v2 << shift))

(*val cast bool -> bit effect pure cast_bool_bit
val cast bit -> int effect pure cast_bit_int *)
function forall Nat 'n, Nat 'm, Nat 'o, 'n <= 0, 'm <= 'o. ([|0:'o|])  negative_to_zero (([|'n:'m|]) x) =
         if x < 0 then 0 else x

typedef byte = bit[8]
typedef qword = bit[64]
typedef regn  = [|15|]
typedef byte_stream = list<byte>
typedef ostream = option<byte_stream>

(* --------------------------------------------------------------------------
   Registers
   -------------------------------------------------------------------------- *)

(* Program Counter *)

register qword RIP

(* General purpose registers *)

register qword RAX (* 0 *)
register qword RCX (* 1 *)
register qword RDX (* 2 *)
register qword RBX (* 3 *)
register qword RSP (* 4 *)
register qword RBP (* 5 *)
register qword RSI (* 6 *)
register qword RDI (* 7 *)
register qword R8
register qword R9
register qword R10
register qword R11
register qword R12
register qword R13
register qword R14
register qword R15

let (vector<0,16,inc,(register<qword>)>) REG =
  [RAX,RCX,RDX,RBX,RSP,RBP,RSI,RDI,R8,R9,R10,R11,R12,R13,R14,R15]

(* Flags *)

register bit[1] CF
register bit[1] PF
register bit[1] AF
register bit[1] ZF
register bit[1] SF
register bit[1] OF

(* --------------------------------------------------------------------------
   Memory
   -------------------------------------------------------------------------- *)

val extern forall Nat 'n. (qword, [|'n|]) -> (bit[8 * 'n]) effect { rmem } rMEM



val extern forall Nat 'n. ( bit[64] , [|'n|]) -> unit effect { eamem } MEMea
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> unit effect { wmv } MEMval
val extern unit -> unit effect { barr } X86_MFENCE

function forall Nat 'n. unit effect {eamem, wmv} wMEM ((qword) addr, ([|'n|]) len, (bit[8 * 'n]) data) = {
         MEMea(addr, len);
         MEMval(addr, len, data);
}

(* --------------------------------------------------------------------------
   Helper functions
   -------------------------------------------------------------------------- *)

(* Instruction addressing modes *)

typedef wsize = const union {
  bool Sz8;
  unit Sz16;
  unit Sz32;
  unit Sz64;
}

typedef base = const union {
  unit NoBase;
  unit RipBase;
  regn RegBase;
}

typedef scale_index = (bit[2],regn)

typedef rm = const union {
  regn                             Reg;
  (option<scale_index>,base,qword) Mem;
}

typedef dest_src = const union {
  (rm,qword) Rm_i;
  (rm,regn)  Rm_r;
  (regn,rm)  R_rm;
}

typedef imm_rm = const union {
  rm    Rm;
  qword Imm;
}

typedef monop_name = enumerate { Dec; Inc; Not; Neg }

typedef binop_name = enumerate {
  Add; Or; Adc; Sbb; And; Sub; Xor; Cmp; Rol; Ror; Rcl; Rcr; Shl; Shr; Test; Sar
}

function binop_name opc_to_binop_name ((bit[4]) opc) =
  switch opc
  {
    case 0x0 -> Add
    case 0x1 -> Or
    case 0x2 -> Adc
    case 0x3 -> Sbb
    case 0x4 -> And
    case 0x5 -> Sub
    case 0x6 -> Xor
    case 0x7 -> Cmp
    case 0x8 -> Rol
    case 0x9 -> Ror
    case 0xa -> Rcl
    case 0xb -> Rcr
    case 0xc -> Shl
    case 0xd -> Shr
    case 0xe -> Test
    case 0xf -> Sar
  }

typedef cond = enumerate {
  O; NO; B; NB; E; NE; NA; A; S; NS; P; NP; L; NL; NG; G; ALWAYS
}

function cond bv_to_cond ((bit[4]) v) =
  switch v
  {
    case 0x0 -> O
    case 0x1 -> NO
    case 0x2 -> B
    case 0x3 -> NB
    case 0x4 -> E
    case 0x5 -> NE
    case 0x6 -> NA
    case 0x7 -> A
    case 0x8 -> S
    case 0x9 -> NS
    case 0xa -> P
    case 0xb -> NP
    case 0xc -> L
    case 0xd -> NL
    case 0xe -> NG
    case 0xf -> G
  }

(* Effective addresses *)

typedef ea = const union {
  (wsize,qword) Ea_i;
  (wsize,regn)  Ea_r;
  (wsize,qword) Ea_m;
}

function qword ea_index ((option<scale_index>) index) =
  switch (index) {
    case None -> 0x0000000000000000
    case (Some(scale, idx)) ->
      let x = (qword) (0x0000000000000001 << scale) in
      let y = (qword) (REG[idx]) in
      let z = (bit[128]) (x * y) in
      z[63 .. 0]
  }

function qword ea_base ((base) b) =
  switch b {
    case NoBase -> 0x0000000000000000
    case RipBase -> RIP
    case (RegBase(b)) -> REG[b]
  }

function ea ea_rm ((wsize) sz, (rm) r) =
  switch r {
    case (Reg(n)) -> Ea_r (sz, n)
    case (Mem(idx, b, d)) -> Ea_m (sz, ea_index(idx) + (qword) (ea_base(b) + d))
  }

function ea ea_dest ((wsize) sz, (dest_src) ds) =
  switch ds {
    case (Rm_i (v, _)) -> ea_rm (sz, v)
    case (Rm_r (v, _)) -> ea_rm (sz, v)
    case (R_rm (v, _)) -> Ea_r (sz, v)
  }

function ea ea_src ((wsize) sz, (dest_src) ds) =
  switch ds {
    case (Rm_i (_, v)) -> Ea_i (sz, v)
    case (Rm_r (_, v)) -> Ea_r (sz, v)
    case (R_rm (_, v)) -> ea_rm (sz, v)
  }

function ea ea_imm_rm ((imm_rm) i_rm) =
  switch i_rm {
    case (Rm (v)) -> ea_rm (Sz64, v)
    case (Imm (v)) -> Ea_i (Sz64, v)
  }

function qword restrict_size ((wsize) sz, (qword) imm) =
  switch sz {
    case (Sz8(_)) -> imm & 0x00000000000000FF
    case Sz16     -> imm & 0x000000000000FFFF
    case Sz32     -> imm & 0x00000000FFFFFFFF
    case Sz64     -> imm
  }

function regn sub4 ((regn) r) = negative_to_zero (r - 4)

function qword effect { rreg, rmem } EA ((ea) e) =
  switch e {
    case (Ea_i(sz,i)) -> restrict_size(sz,i)
    case (Ea_r((Sz8(have_rex)),r)) ->
      if have_rex | r < 4 (* RSP *) | r > 7 (* RDI *) then
        REG[r]
      else
        (REG[sub4 (r)] >> 8) & 0x00000000000000FF
    case (Ea_r(sz,r)) -> restrict_size(sz, REG[r])
    case (Ea_m((Sz8(_)),a)) -> EXTZ (rMEM(a, 1))
    case (Ea_m(Sz16,a)) -> EXTZ (rMEM(a, 2))
    case (Ea_m(Sz32,a)) -> EXTZ (rMEM(a, 4))
    case (Ea_m(Sz64,a)) -> rMEM(a, 8)
  }

function unit effect { wmem, wreg, escape } wEA ((ea) e, (qword) w) =
  switch e {
    case (Ea_i(_,_)) -> exit ()
    case (Ea_r((Sz8(have_rex)),r)) ->
      if have_rex | r < 4 (* RSP *) | r > 7 (* RDI *) then
      {
        (qword) regr := REG[r];
        regr[7 .. 0] := w[7 .. 0];
        REG[r] := regr
      }
      else
      {
        (qword) regr := REG[sub4(r)];
        regr[15 .. 8] := (vector<15,8,dec,bit>) (w[7 .. 0]);
        REG[sub4(r)] := regr
      }
    case (Ea_r(Sz16,r)) ->
      {
        (qword) regr := REG[r];
        regr[15 .. 8] := w[15 .. 8];
        REG[r] := regr
      }
    case (Ea_r(Sz32,r)) -> REG[r] := (qword) (EXTZ (w[31 .. 0]))
    case (Ea_r(Sz64,r)) -> REG[r] := w
    case (Ea_m((Sz8(_)),a)) -> wMEM(a, 1, w[7 .. 0])
    case (Ea_m(Sz16,a)) -> wMEM(a, 2, w[15 .. 0])
    case (Ea_m(Sz32,a)) -> wMEM(a, 4, w[31 .. 0])
    case (Ea_m(Sz64,a)) -> wMEM(a, 8, w)
  }

function (ea, qword, qword) read_dest_src_ea ((wsize) sz, (dest_src) ds) =
  let e = ea_dest (sz, ds) in
  (e, EA(e), EA(ea_src(sz, ds)))

function qword call_dest_from_ea ((ea) e) =
  switch e {
    case (Ea_i(_, i)) -> RIP + i
    case (Ea_r(_, r)) -> REG[r]
    case (Ea_m(_, a)) -> rMEM(a, 8)
  }

function qword get_ea_address ((ea) e) = (* XXX rmn30 looks broken *)
  switch e {
    case (Ea_i(_, i)) -> 0x0000000000000000
    case (Ea_r(_, r)) -> 0x0000000000000000
    case (Ea_m(_, a)) -> 0x0000000000000000
  }

function unit jump_to_ea ((ea) e) = RIP := call_dest_from_ea(e)

(* EFLAG updates *)

function bit byte_parity ((byte) b) =
{
  (int) acc := 0;
  foreach (i from 0 to 7) acc := acc + (int) (b[i]);
  (bit) (acc mod 2 == 0)
}

function [|64|] size_width ((wsize) sz) =
  switch sz {
    case (Sz8(_)) -> 8
    case Sz16 -> 16
    case Sz32 -> 32
    case Sz64 -> 64
  }

function [|63|] size_width_sub1 ((wsize) sz) =
  switch sz {
    case (Sz8(_)) -> 7
    case Sz16 -> 15
    case Sz32 -> 31
    case Sz64 -> 63
  }

(* XXXXX
function bit word_size_msb ((wsize) sz, (qword) w) = w[size_width(sz) - 1]
*)

function bit word_size_msb ((wsize) sz, (qword) w) = w[size_width_sub1(sz)]

function unit write_PF ((qword) w) = PF := byte_parity (w[7 .. 0])

function unit write_SF ((wsize) sz, (qword) w) = SF := word_size_msb (sz, w)

function unit write_ZF ((wsize) sz, (qword) w) =
  ZF := (bit)
         (switch sz {
            case (Sz8(_)) -> w[7 .. 0] == 0x00
            case Sz16 -> w[15 .. 0] == 0x0000
            case Sz32 -> w[31 .. 0] == 0x00000000
            case Sz64 -> w == 0x0000000000000000
          })

function unit write_arith_eflags_except_CF_OF ((wsize) sz, (qword) w) =
{
  AF := undefined;
  write_PF(w);
  write_SF(sz, w);
  write_ZF(sz, w);
}

function unit write_arith_eflags ((wsize) sz, (qword) w, (bit) c, (bit) x) =
{
  CF := c;
  OF := x;
  write_arith_eflags_except_CF_OF (sz, w)
}

function unit write_logical_eflags ((wsize) sz, (qword) w) =
  write_arith_eflags (sz, w, bitzero, bitzero)

function unit erase_eflags () =
{
  AF := undefined;
  CF := undefined;
  OF := undefined;
  PF := undefined;
  SF := undefined;
  ZF := undefined;
}

function nat value_width ((wsize) sz) = 2 ** size_width(sz)

function bit word_signed_overflow_add ((wsize) sz, (qword) a, (qword) b) =
  (bit) (word_size_msb (sz, a) == word_size_msb (sz, b) &
         word_size_msb (sz, a + b) != word_size_msb (sz, a))

function bit word_signed_overflow_sub ((wsize) sz, (qword) a, (qword) b) =
  (bit) (word_size_msb (sz, a) != word_size_msb (sz, b) &
         word_size_msb (sz, a - b) != word_size_msb (sz, a))

function (qword, bit, bit) add_with_carry_out ((wsize) sz, (qword) a, (qword) b) =
  (a + b, (bit) ((int) (value_width (sz)) <= unsigned(a) + unsigned(b)),
   word_signed_overflow_add (sz, a, b))

function (qword, bit, bit) sub_with_borrow ((wsize) sz, (qword) a, (qword) b) =
  (a - b, (bit) (a < b), word_signed_overflow_sub (sz, a, b))

function unit write_arith_result ((wsize) sz, (qword) w, (bit) c, (bit) x, (ea) e) =
{
  write_arith_eflags (sz, w, c, x);
  wEA (e) := w;
}

function unit write_arith_result_no_CF_OF ((wsize) sz, (qword) w, (ea) e) =
{
  write_arith_eflags_except_CF_OF (sz, w);
  wEA (e) := w;
}

function unit write_logical_result ((wsize) sz, (qword) w, (ea) e) =
{
  write_arith_eflags_except_CF_OF (sz, w);
  wEA (e) := w;
}

function unit write_result_erase_eflags ((qword) w, (ea) e) =
{
  erase_eflags ();
  wEA (e) := w;
}

function qword effect { escape } sign_extension ((qword) w, (wsize) size1, (wsize) size2) =
{
  (qword) x := w;
  switch (size1, size2) {
    case ((Sz8(_)), Sz16) -> x[15 .. 0] := (bit[16]) (EXTS (w[7 .. 0]))
    case ((Sz8(_)), Sz32) -> x[31 .. 0] := (bit[32]) (EXTS (w[7 .. 0]))
    case ((Sz8(_)), Sz64) -> x := (qword) (EXTS (w[7 .. 0]))
    case (Sz16, Sz32) -> x[31 .. 0] := (bit[32]) (EXTS (w[15 .. 0]))
    case (Sz16, Sz64) -> x := (qword) (EXTS (w[15 .. 0]))
    case (Sz32, Sz64) -> x := (qword) (EXTS (w[31 .. 0]))
    case _ -> undefined
  };
  x;
}

function [|64|] mask_shift ((wsize) sz, (qword) w) =
  if sz == Sz64 then w[5 .. 0] else w[4 .. 0]

function qword rol ((wsize) sz, (qword) a, (qword) b) =
  switch sz {
    case (Sz8(_)) -> EXTZ (ROL8 (a[7 .. 0], b[2 .. 0]))
    case Sz16 -> EXTZ (ROL16 (a[15 .. 0], b[3 .. 0]))
    case Sz32 -> EXTZ (ROL32 (a[31 .. 0], b[4 .. 0]))
    case Sz64 -> ROL64 (a, b[5 .. 0])
  }

function qword ror ((wsize) sz, (qword) a, (qword) b) =
  switch sz {
    case (Sz8(_)) -> EXTZ (ROR8 (a[7 .. 0], b[2 .. 0]))
    case Sz16 -> EXTZ (ROR16 (a[15 .. 0], b[3 .. 0]))
    case Sz32 -> EXTZ (ROR32 (a[31 .. 0], b[4 .. 0]))
    case Sz64 -> ROR64 (a, b[5 .. 0])
  }

function qword sar ((wsize) sz, (qword) a, (qword) b) =
  switch sz {
    case (Sz8(_)) -> EXTZ (ASR8 (a[7 .. 0], b[2 .. 0]))
    case Sz16 -> EXTZ (ASR16 (a[15 .. 0], b[3 .. 0]))
    case Sz32 -> EXTZ (ASR32 (a[31 .. 0], b[4 .. 0]))
    case Sz64 -> ASR64 (a, b[5 .. 0])
  }

function unit write_binop ((wsize) sz, (binop_name) bop, (qword) a, (qword) b, (ea) e) =
  switch bop {
    case Add -> let (w,c,x) = add_with_carry_out (sz, a, b) in
                write_arith_result (sz, w, c, x, e)
    case Sub -> let (w,c,x) = sub_with_borrow (sz, a, b) in
                write_arith_result (sz, w, c, x, e)
    case Cmp -> let (w,c,x) = sub_with_borrow (sz, a, b) in
                write_arith_eflags (sz, w, c, x)
    case Test -> write_logical_eflags (sz, a & b)
    case And -> write_logical_result (sz, a & b, e) (* XXX rmn30 wrong flags? *)
    case Xor -> write_logical_result (sz, a ^ b, e)
    case Or  -> write_logical_result (sz, a | b, e)
    case Rol -> write_result_erase_eflags (rol (sz, a, b), e)
    case Ror -> write_result_erase_eflags (ror (sz, a, b), e)
    case Sar -> write_result_erase_eflags (sar (sz, a, b), e)
    case Shl -> write_result_erase_eflags (a << mask_shift (sz, b), e)
    case Shr -> write_result_erase_eflags (a >> mask_shift (sz, b), e)
    case Adc ->
      {
        let carry = (bit) CF in
        let (qword) result = a + (qword) (b + carry) in
        {
          CF := (bit) ((int) (value_width (sz)) <= unsigned(a) + unsigned(b));
          OF := undefined;
          write_arith_result_no_CF_OF (sz, result, e);
        }
      }
    case Sbb ->
      {
        let carry = (bit) CF in
        let (qword) result = a - (qword) (b + carry) in
        {
          CF := (bit) (unsigned(a) < unsigned(b) + (int) carry);
          OF := undefined;
          write_arith_result_no_CF_OF (sz, result, e);
        }
      }
    case _ -> exit ()
  }

function unit write_monop ((wsize) sz, (monop_name) mop, (qword) a, (ea) e) =
  switch mop {
    case Not -> wEA(e) := ~(a)
    case Dec -> write_arith_result_no_CF_OF (sz, a - 1, e) 
    case Inc -> write_arith_result_no_CF_OF (sz, a + 1, e)(* XXX rmn30 should set OF *)
    case Neg -> { write_arith_result_no_CF_OF (sz, 0 - a, e);
                  CF := undefined;
                }
  }

function bool read_cond ((cond) c) =
  switch c {
    case A  -> ~(CF) & ~(ZF)
    case NB -> ~(CF)
    case B  -> CF
    case NA -> CF | (bit) ZF
    case E  -> ZF
    case G  -> ~(ZF) & (SF == OF)
    case NL -> SF == OF
    case L  -> SF != OF
    case NG -> ZF | SF != OF
    case NE -> ~(ZF)
    case NO -> ~(OF)
    case NP -> ~(PF)
    case NS -> ~(SF)
    case O  -> OF
    case P  -> PF
    case S  -> SF
    case ALWAYS -> true
  }

function qword pop_aux () =
  let top = rMEM(RSP, 8) in
  {
    RSP := RSP + 8;
    top;
  }

function unit push_aux ((qword) w) =
{
  RSP := RSP - 8;
  wMEM(RSP, 8) := w;
}

function unit pop ((rm) r) = wEA (ea_rm (Sz64,r)) := pop_aux()
function unit pop_rip () = RIP := pop_aux()
function unit push ((imm_rm) i) = push_aux (EA (ea_imm_rm (i)))
function unit push_rip () = push_aux (RIP)

function unit drop ((qword) i) = if i[7 ..0] != 0 then () else RSP := RSP + i

(* --------------------------------------------------------------------------
   Instructions
   -------------------------------------------------------------------------- *)

scattered function unit execute
scattered typedef ast = const union

val ast -> unit effect {escape, rmem, rreg, undef, eamem, wmv, wreg, barr} execute

(* ==========================================================================
      Binop
   ========================================================================== *)

union ast member (binop_name,wsize,dest_src) Binop

function clause execute (Binop (bop,sz,ds)) =
  let (e, val_dst, val_src) = read_dest_src_ea (sz, ds) in
  write_binop (sz, bop, val_dst, val_src, e)

(* ==========================================================================
      CALL
   ========================================================================== *)

union ast member imm_rm CALL

function clause execute (CALL (i)) =
{
  push_rip();
  jump_to_ea (ea_imm_rm (i))
}

(* ==========================================================================
      CLC
   ========================================================================== *)

union ast member unit CLC

function clause execute CLC = CF := false

(* ==========================================================================
      CMC
   ========================================================================== *)

union ast member unit CMC

function clause execute CMC = CF := ~(CF)

(* ==========================================================================
      CMPXCHG
   ========================================================================== *)

union ast member (wsize,rm,regn) CMPXCHG

function clause execute (CMPXCHG (sz,r,n)) =
  let src = Ea_r(sz, n) in
  let acc = Ea_r(sz, 0) in (* RAX *)
  let dst = ea_rm(sz, r) in
  let val_dst = EA(dst) in
  let val_acc = EA(src) in
  {
    write_binop (sz, Cmp, val_acc, val_dst, src); 
    if val_acc == val_dst then
      wEA(dst) := EA (src)
    else
      wEA(acc) := val_dst;
  }

(* ==========================================================================
      DIV
   ========================================================================== *)

union ast member (wsize,rm) DIV

function clause execute (DIV (sz,r)) =
  let w = (int) (value_width(sz)) in
  let eax = Ea_r(sz, 0) in (* RAX *)
  let edx = Ea_r(sz, 2) in (* RDX *)
  let n = unsigned(EA(edx)) * w + unsigned(EA(eax)) in
  let d = unsigned(EA(ea_rm(sz, r))) in
  let q = n quot d in
  let m = n mod d in
  if d == 0 | w < q then exit ()
  else
  {
    wEA(eax) := (qword) q;
    wEA(edx) := (qword) m;
    erase_eflags();
  }

(* ==========================================================================
      HLT -- halt instruction used to end test in RMEM
   ========================================================================== *)

union ast member unit HLT

function clause execute (HLT) = ()


(* ==========================================================================
      Jcc
   ========================================================================== *)

union ast member (cond,qword) Jcc

function clause execute (Jcc (c,i)) =
  if read_cond (c) then RIP := RIP + i else ()

(* ==========================================================================
      JMP
   ========================================================================== *)

union ast member rm JMP

function clause execute (JMP (r)) = RIP := EA (ea_rm (Sz64, r))

(* ==========================================================================
      LEA
   ========================================================================== *)

union ast member (wsize,dest_src) LEA

function clause execute (LEA (sz,ds)) =
  let src = ea_src (sz, ds) in
  let dst = ea_dest (sz, ds) in
  wEA(dst) := get_ea_address (src)

(* ==========================================================================
      LEAVE
   ========================================================================== *)

union ast member unit LEAVE

function clause execute LEAVE =
{
  RSP := RBP;
  pop (Reg (5)); (* RBP *)
}

(* ==========================================================================
      LOOP
   ========================================================================== *)

union ast member (cond,qword) LOOP

function clause execute (LOOP (c,i)) =
{
  RCX := RCX - 1;
  if RCX != 0 & read_cond (c) then RIP := RIP + i else ();
}

(* ==========================================================================
      MFENCE
   ========================================================================== *)

union ast member unit MFENCE

function clause execute (MFENCE) =
  X86_MFENCE ()

(* ==========================================================================
      Monop
   ========================================================================== *)

union ast member (monop_name,wsize,rm) Monop

function clause execute (Monop (mop,sz,r)) =
  let e = ea_rm (sz, r) in write_monop (sz, mop, EA(e), e)

(* ==========================================================================
      MOV
   ========================================================================== *)

union ast member (cond,wsize,dest_src) MOV

function clause execute (MOV (c,sz,ds)) =
  if read_cond (c) then
    let src = ea_src (sz, ds) in
    let dst = ea_dest (sz, ds) in
    wEA(dst) := EA(src)
  else ()

(* ==========================================================================
      MOVSX
   ========================================================================== *)

union ast member (wsize,dest_src,wsize) MOVSX

function clause execute (MOVSX (sz1,ds,sz2)) =
  let src = ea_src (sz1, ds) in
  let dst = ea_dest (sz2, ds) in
  wEA(dst) := sign_extension (EA(src), sz1, sz2)

(* ==========================================================================
      MOVZX
   ========================================================================== *)

union ast member (wsize,dest_src,wsize) MOVZX

function clause execute (MOVZX (sz1,ds,sz2)) =
  let src = ea_src (sz1, ds) in
  let dst = ea_dest (sz2, ds) in
  wEA(dst) := EA(src)

(* ==========================================================================
      MUL
   ========================================================================== *)

union ast member (wsize,rm) MUL

function clause execute (MUL (sz,r)) =
  let eax = Ea_r (sz, 0) in (* RAX *)
  let val_eax = EA(eax) in
  let val_src = EA(ea_rm (sz, r)) in
  switch sz {
    case (Sz8(_)) -> wEA(Ea_r(Sz16,0)) := (val_eax * val_src)[63 .. 0]
    case _ ->
      let m = val_eax * val_src in
      let edx = Ea_r (sz, 2) in (* RDX *)
      {
        wEA(eax) := m[63 .. 0];
        wEA(edx) := (m >> size_width(sz))[63 .. 0]
      }
  }

(* ==========================================================================
      NOP
   ========================================================================== *)

union ast member nat NOP

function clause execute (NOP (_)) = ()

(* ==========================================================================
      POP
   ========================================================================== *)

union ast member rm POP

function clause execute (POP (r)) = pop(r)

(* ==========================================================================
      PUSH
   ========================================================================== *)

union ast member imm_rm PUSH

function clause execute (PUSH (i)) = push(i)

(* ==========================================================================
      RET
   ========================================================================== *)

union ast member qword RET

function clause execute (RET (i)) =
{
  pop_rip();
  drop(i);
}

(* ==========================================================================
      SET
   ========================================================================== *)

union ast member (cond,bool,rm) SET

function clause execute (SET (c,b,r)) =
  wEA(ea_rm(Sz8(b),r)) := if read_cond (c) then 1 else 0

(* ==========================================================================
      STC
   ========================================================================== *)

union ast member unit STC

function clause execute STC = CF := true

(* ==========================================================================
      XADD
   ========================================================================== *)

union ast member (wsize,rm,regn) XADD

function clause execute (XADD (sz,r,n)) =
  let src = Ea_r (sz, n) in
  let dst = ea_rm (sz, r) in
  let val_src = EA(src) in
  let val_dst = EA(dst) in
  {
    wEA(src) := val_dst;
    write_binop (sz, Add, val_src, val_dst, dst);
  }

(* ==========================================================================
      XCHG
   ========================================================================== *)

union ast member (wsize,rm,regn) XCHG

function clause execute (XCHG (sz,r,n)) =
  let src = Ea_r (sz, n) in
  let dst = ea_rm (sz, r) in
  let val_src = EA(src) in
  let val_dst = EA(dst) in
  {
    wEA(src) := val_dst;
    wEA(dst) := val_src;
  }

end ast
end execute

(* --------------------------------------------------------------------------
   Decoding
   -------------------------------------------------------------------------- *)
(*
function (qword,ostream) oimmediate8 ((ostream) strm) =
  switch strm {
    case (Some (b :: t)) -> ((qword) (EXTS(b)), Some (t))
    case _ -> ((qword) undefined, (ostream) None)
  }

function (qword,ostream) immediate8 ((byte_stream) strm) =
  oimmediate8 (Some (strm))

function (qword,ostream) immediate16 ((byte_stream) strm) =
  switch strm {
    case b1 :: b2 :: t -> ((qword) (EXTS(b2 : b1)), Some (t))
    case _ -> ((qword) undefined, (ostream) None)
  }

function (qword,ostream) immediate32 ((byte_stream) strm) =
  switch strm {
    case b1 :: b2 :: b3 :: b4 :: t ->
      ((qword) (EXTS(b4 : b3 : b2 : b1)), Some (t))
    case _ -> ((qword) undefined, (ostream) None)
  }

function (qword,ostream) immediate64 ((byte_stream) strm) =
  switch strm {
    case b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: t ->
      ((qword) (EXTS(b8 : b7 : b6 : b5 : b4 : b3 : b2 : b1)), Some (t))
    case _ -> ((qword) undefined, (ostream) None)
  }

function (qword, ostream) immediate ((wsize) sz, (byte_stream) strm) =
   switch sz {
      case (Sz8 (_)) -> immediate8 (strm)
      case Sz16      -> immediate16 (strm)
      case _         -> immediate32 (strm)
   }

function (qword, ostream) oimmediate ((wsize) sz, (ostream) strm) =
   switch strm {
      case (Some (s)) -> immediate (sz, s)
      case None       -> ((qword) undefined, (ostream) None)
   }

function (qword, ostream) full_immediate ((wsize) sz, (byte_stream) strm) =
  if sz == Sz64 then immediate64 (strm) else immediate (sz, strm)

(* - Parse ModR/M and SIB bytes --------------------------------------------- *)

typedef REX = register bits [3 : 0] {
  3 : W;
  2 : R;
  1 : X;
  0 : B
}

function regn rex_reg ((bit[1]) b, (bit[3]) r) = unsigned(b : r)

function (qword, ostream) read_displacement ((bit[2]) Mod, (byte_stream) strm) =
   if Mod == 0b01
      then immediate8 (strm)
   else if Mod == 0b10
      then immediate32 (strm)
   else (0x0000000000000000, (Some (strm)))

function (qword, ostream)
  read_sib_displacement ((bit[2]) Mod, (byte_stream) strm) =
  if Mod == 0b01 then immediate8 (strm) else immediate32 (strm)

function (rm, ostream)
   read_SIB ((REX) rex, (bit[2]) Mod, (byte_stream) strm) =
   switch strm {
     case ((bit[2]) SS : (bit[3]) Index : (bit[3]) Base) :: strm1 ->
        (let bbase = rex_reg (rex.B, Base) in
         let index = rex_reg (rex.X, Index) in
         let scaled_index = if index == 4 (* RSP *) then
                               (option<scale_index>) None
                            else let x = (scale_index) (SS, index) in
                               Some (x) in
          (if bbase == 5 (* RBP *)
              then let (displacement, strm2) =
                      read_sib_displacement (Mod, strm1) in
                   let bbase = if Mod == 0b00 then NoBase else RegBase (bbase)
                   in
                      (Mem (scaled_index, bbase, displacement), strm2)
           else let (displacement, strm2) = read_displacement (Mod, strm1) in
              (Mem (scaled_index, RegBase (bbase), displacement), strm2)))
     case _ -> ((rm) undefined, (ostream) None)
   }

function (regn, rm, ostream) read_ModRM ((REX) rex, (byte_stream) strm) =
   switch strm {
     case (0b00 : (bit[3]) RegOpc : 0b101) :: strm1 ->
       let (displacement, strm2) = immediate32 (strm1) in
         (rex_reg (rex.R, RegOpc), Mem (None, RipBase, displacement), strm2)
     case (0b11 : (bit[3]) REG : (bit[3]) RM) :: strm1 ->
         (rex_reg (rex.R, REG), Reg (rex_reg (rex.B, RM)), Some (strm1))
     case ((bit[2]) Mod : (bit[3]) RegOpc : 0b100) :: strm1 ->
       let (sib, strm2) = read_SIB (rex, Mod, strm1) in
         (rex_reg (rex.R, RegOpc), sib, strm2)
     case ((bit[2]) Mod : (bit[3]) RegOpc : (bit[3]) RM) :: strm1 ->
       let (displacement, strm2) = read_displacement (Mod, strm1) in
         (rex_reg (rex.R, RegOpc),
          Mem (None, RegBase (rex_reg (rex.B, RM)), displacement),
          strm2)
     case _ -> ((regn) undefined, (rm) undefined, (ostream) None)
   }

function (bit[3], rm, ostream)
   read_opcode_ModRM ((REX) rex, (byte_stream) strm) =
  let (opcode, r, strm1) = read_ModRM (rex, strm) in
    ((bit[3]) (cast_int_vec((int) opcode mod 8)), r, strm1)

(* - Prefixes --------------------------------------------------------------- *)

typedef prefix = [|5|]

function prefix prefix_group ((byte) b) =
  switch b {
    case 0xf0 -> 1
    case 0xf2 -> 1
    case 0xf3 -> 1
    case 0x26 -> 2
    case 0x2e -> 2
    case 0x36 -> 2
    case 0x3e -> 2
    case 0x64 -> 2
    case 0x65 -> 2
    case 0x66 -> 3
    case 0x67 -> 4
    case _ -> if b[7 .. 4] == 0b0100 then 5 else 0
  }

typedef atuple = (byte_stream, bool, REX, byte_stream)

val (list<prefix>, byte_stream, byte_stream) -> option<atuple> effect {undef} read_prefix

function rec option<atuple> read_prefix
  ((list<prefix>) s, (byte_stream) p, (byte_stream) strm) =
    switch strm {
      case h :: strm1 ->
         let group = prefix_group (h) in
           if group == 0 then
              let x = (p, false, (REX) 0b0000, strm) in Some (x)
           else if group == 5 then
              let x = (p, true, (REX) (h[3 .. 0]), strm1) in Some (x)
           else if ismember (group, s) then
              None
           else
              read_prefix (group :: s, h :: p, strm1)
      case _ -> let x = (p, false, (REX) undefined, strm) in Some (x)
    }

function  option<atuple> read_prefixes ((byte_stream) strm) =
   read_prefix ([||||], [||||], strm)

function wsize op_size ((bool) have_rex, (bit[1]) w, (bit[1]) v, (bool) override) =
  if v == 1 then
    Sz8 (have_rex)
  else if w == 1 then
    Sz64
  else if override then
    Sz16
  else
    Sz32

function bool is_mem ((rm) r) =
  switch r {case (Mem (_, _, _)) -> true case _ -> false}

(* - Decoder ---------------------------------------------------------------- *)

function (ast, ostream) decode_aux
  ((byte_stream) strm, (bool) have_rex, (REX) rex, (bool) op_size_override) =
  switch strm
  {
    case (0b00 : (bit[3]) opc : 0b0 : (bit[1]) x : (bit[1]) v) :: strm2 ->
      let (reg, r, strm3) = read_ModRM (rex, strm2) in
      let sz = op_size (have_rex, rex.W, v, op_size_override) in
      let binop = opc_to_binop_name (EXTZ (opc)) in
      let src_dst = if x == 0 then Rm_r (r, reg) else R_rm (reg, r) in
      (Binop (binop, sz, src_dst), strm3)
    case (0b00 : (bit[3]) opc : 0b10 : (bit[1]) v) :: strm2 ->
      let sz = op_size (have_rex, rex.W, v, op_size_override) in
      let binop = opc_to_binop_name (EXTZ (opc)) in
      let (imm, strm3) = immediate (sz, strm2) in
      (Binop (binop, sz, Rm_i (Reg (0), imm)), strm3)
    case (0x5 : (bit[1]) b : (bit[3]) r) :: strm2 ->
      let reg = Reg (([|15|]) (rex.B : r)) in
      (if b == 0b0 then PUSH (Rm (reg)) else POP (reg), Some (strm2))
    case 0x63 :: strm2 ->
      let (reg, r, strm3) = read_ModRM (rex, strm2) in
      (MOVSX (Sz32, R_rm (reg, r), Sz64), strm3)
    case (0x6 : 0b10 : (bit[1]) b : 0b0) :: strm2 ->
      let (imm, strm3) = if b == 1 then immediate8 (strm2)
                         else immediate32 (strm2) in
      (PUSH (Imm (imm)), strm3)
    case (0x7 : (bit[4]) c) :: strm2 ->
      let (imm, strm3) = immediate8 (strm2) in
      (Jcc (bv_to_cond (c), imm), strm3)
    case (0x8 : 0b000 : (bit[1]) v) :: strm2 ->
      let sz = op_size (have_rex, rex.W, v, op_size_override) in
      let (opc, r, strm3) = read_opcode_ModRM (rex, strm2) in
      let (imm, strm4) = oimmediate (sz, strm3) in
      let binop = opc_to_binop_name (EXTZ (opc)) in
      (Binop (binop, sz, Rm_i (r, imm)), strm4)
    case 0x83 :: strm2 ->
      let sz = op_size (have_rex, rex.W, 1, op_size_override) in
      let (opc, r, strm3) = read_opcode_ModRM (rex, strm2) in
      let (imm, strm4) = oimmediate (sz, strm3) in
      let binop = opc_to_binop_name (EXTZ (opc)) in
      (Binop (binop, sz, Rm_i (r, imm)), strm4)
    case (0x8 : 0b010 : (bit[1]) v) :: strm2 ->
      let sz = op_size (have_rex, rex.W, v, op_size_override) in
      let (reg, r, strm3) = read_ModRM (rex, strm2) in
      (Binop (Test, sz, Rm_r (r, reg)), strm3)
    case (0x8 : 0b011 : (bit[1]) v) :: strm2 ->
      let sz = op_size (have_rex, rex.W, v, op_size_override) in
      let (reg, r, strm3) = read_ModRM (rex, strm2) in
      (XCHG (sz, r, reg), strm3)
    case (0x8 : 0b10 : (bit[1]) x : (bit[1]) v) :: strm2 ->
      let (reg, r, strm3) = read_ModRM (rex, strm2) in
      let sz = op_size (have_rex, rex.W, v, op_size_override) in
      let src_dst = if x == 0 then Rm_r (r, reg) else R_rm (reg, r) in
      (MOV (ALWAYS, sz, src_dst), strm3)
    case 0x8d :: strm2 ->
      let sz = op_size (true, rex.W, 1, op_size_override) in
      let (reg, r, strm3) = read_ModRM (rex, strm2) in
      if is_mem (r) then (LEA (sz, R_rm (reg, r)), strm3) else exit ()
    case 0x8f :: strm2 ->
      let (opc, r, strm3) = read_opcode_ModRM (rex, strm2) in
      if opc == 0 then (POP (r), strm3) else exit ()
    case (0x9 : 0b0 : (bit[3]) r) :: strm2 ->
      let sz = op_size (true, rex.W, 1, op_size_override) in
      let reg = rex_reg (rex.B, r) in
      if reg == 0 then
        (NOP (listlength (strm)), Some (strm2))
      else
        (XCHG (sz, Reg (0), reg), Some (strm2))
    case (0xa : 0b100 : (bit[1]) v) :: strm2 ->
      let sz = op_size (true, rex.W, v, op_size_override) in
      let (imm, strm3) = immediate (sz, strm2) in
      (Binop (Test, sz, Rm_i (Reg (0), imm)), strm3)
    case (0xb : (bit[1]) v : (bit[3]) r) :: strm2 ->
      let sz = op_size (have_rex, rex.W, v, op_size_override) in
      let (imm, strm3) = full_immediate (sz, strm2) in
      let reg = rex_reg (rex.B, r) in
      (MOV (ALWAYS, sz, Rm_i (Reg (reg), imm)), strm3)
    case (0xc : 0b000 : (bit[1]) v) :: strm2 ->
      let sz = op_size (have_rex, rex.W, v, op_size_override) in
      let (opc, r, strm3) = read_opcode_ModRM (rex, strm2) in
      let (imm, strm4) = oimmediate8 (strm3) in
      let binop = opc_to_binop_name (0b1 : opc) in
      if opc == 0b110 then exit ()
      else (Binop (binop, sz, Rm_i (r, imm)), strm4)
    case (0xc : 0b001 : (bit[1]) v) :: strm2 ->
      if v == 0 then
        let (imm, strm3) = immediate16 (strm2) in (RET (imm), strm3)
      else
        (RET (0), Some (strm2))
    case (0xc : 0b011 : (bit[1]) v) :: strm2 ->
      let sz = op_size (have_rex, rex.W, v, op_size_override) in
      let (opc, r, strm3) = read_opcode_ModRM (rex, strm2) in
      let (imm, strm4) = oimmediate (sz, strm3) in
      if opc == 0 then (MOV (ALWAYS, sz, Rm_i (r, imm)), strm4)
      else exit ()
    case 0xc9 :: strm2 ->
      (LEAVE, Some (strm2))
    case (0xd : 0b00 : (bit[1]) b : (bit[1]) v) :: strm2 ->
      let sz = op_size (have_rex, rex.W, v, op_size_override) in
      let (opc, r, strm3) = read_opcode_ModRM (rex, strm2) in
      let shift = if b == 0 then Rm_i (r, 1) else Rm_r (r, 1) in
      let binop = opc_to_binop_name (0b1 : opc) in
      if opc == 0b110 then exit ()
      else (Binop (binop, sz, shift), strm3)
    case (0xe : 0b000 : (bit[1]) b) :: strm2 ->
      let (imm, strm3) = immediate8 (strm2) in
      let cnd = if b == 0 then NE else E in
      (LOOP (cnd, imm), strm3)
    case 0xe2 :: strm2 ->
      let (imm, strm3) = immediate8 (strm2) in
      (LOOP (ALWAYS, imm), strm3)
    case 0xe8 :: strm2 ->
      let (imm, strm3) = immediate32 (strm2) in
      (CALL (Imm (imm)), strm3)
    case (0xe : 0b10 : (bit[1]) b : 0b1) :: strm2 ->
      let (imm, strm3) = if b == 0 then immediate32 (strm2)
                         else immediate8 (strm2) in
      (Jcc (ALWAYS, imm), strm3)
    case 0xf5 :: strm2 -> (CMC, Some (strm2))
    case 0xf8 :: strm2 -> (CLC, Some (strm2))
    case 0xf9 :: strm2 -> (STC, Some (strm2))
    case (0xf : 0b011 : (bit[1]) v) :: strm2 ->
      let sz = op_size (have_rex, rex.W, v, op_size_override) in
      let (opc, r, strm3) = read_opcode_ModRM (rex, strm2) in
      switch opc {
        case 0b000 -> let (imm, strm4) = oimmediate (sz, strm3) in
                      (Binop (Test, sz, Rm_i (r, imm)), strm4)
        case 0b010 -> (Monop (Not, sz, r), strm3)
        case 0b011 -> (Monop (Neg, sz, r), strm3)
        case 0b100 -> (MUL (sz, r), strm3)
        case 0b110 -> (DIV (sz, r), strm3)
        case _ -> exit ()
      }
    case 0xfe :: strm2 ->
      let (opc, r, strm3) = read_opcode_ModRM (rex, strm2) in
      switch opc {
        case 0b000 -> (Monop (Inc, Sz8 (have_rex), r), strm3)
        case 0b001 -> (Monop (Dec, Sz8 (have_rex), r), strm3)
        case _ -> exit ()
      }
    case 0xff :: strm2 ->
      let sz = op_size (have_rex, rex.W, 1, op_size_override) in
      let (opc, r, strm3) = read_opcode_ModRM (rex, strm2) in
      switch opc {
        case 0b000 -> (Monop (Inc, sz, r), strm3)
        case 0b001 -> (Monop (Dec, sz, r), strm3)
        case 0b010 -> (CALL (Rm (r)), strm3)
        case 0b100 -> (JMP (r), strm3)
        case 0b110 -> (PUSH (Rm (r)), strm3)
        case _ -> exit ()
      }
    case 0x0f :: opc :: strm2 ->
      switch opc {
        case 0x1f ->
          let (opc, r, strm3) = read_opcode_ModRM (rex, strm2) in
          (NOP (listlength (strm)), strm3)
        case (0x4 : (bit[4]) c) ->
          let sz = op_size (true, rex.W, 1, op_size_override) in
          let (reg, r, strm3) = read_ModRM (rex, strm2) in
          (MOV (bv_to_cond (c), sz, R_rm (reg, r)), strm3)
        case (0x8 : (bit[4]) c) ->
          let (imm, strm3) = immediate32 (strm2) in
          (Jcc (bv_to_cond (c), imm), strm3)
        case (0x9 : (bit[4]) c) ->
          let (reg, r, strm3) = read_ModRM (rex, strm2) in
          (SET (bv_to_cond (c), have_rex, r), strm3)
        case (0xb : 0b000 : (bit[1]) v) ->
          let sz = op_size (have_rex, rex.W, v, op_size_override) in
          let (reg, r, strm3) = read_ModRM (rex, strm2) in
          (CMPXCHG (sz, r, reg), strm3)
        case (0xc : 0b000 : (bit[1]) v) ->
          let sz = op_size (have_rex, rex.W, v, op_size_override) in
          let (reg, r, strm3) = read_ModRM (rex, strm2) in
          (XADD (sz, r, reg), strm3)
        case (0xb : (bit[1]) s : 0b11 : (bit[1]) v) ->
          let sz2 = op_size (have_rex, rex.W, 1, op_size_override) in
          let sz = if v == 1 then Sz16 else Sz8 (have_rex) in
          let (reg, r, strm3) = read_ModRM (rex, strm2) in
          if s == 1 then
             (MOVSX (sz, R_rm (reg, r), sz2), strm3)
          else
             (MOVZX (sz, R_rm (reg, r), sz2), strm3)
        case _ -> exit ()
      }
    case _ -> exit ()
  }

function (byte_stream, ast, nat) decode ((byte_stream) strm) =
  switch read_prefixes (strm)
  {
    case None -> exit ()
    case (Some (prefixes, have_rex, rex, strm1)) ->
      let op_size_override = ismember (0x66, prefixes) in
      if rex.W == 1 & op_size_override | ismember (0x67, prefixes) then
        exit ()
      else
        switch decode_aux (strm1, have_rex, rex, op_size_override) {
          case (instr, (Some (strm2))) -> (prefixes, instr, listlength (strm2))
          case _ -> exit ()
        }
  }
  *)

let (vector <0, 16, inc, string >) GPRstr =
  ["RAX","RCX","RDX","RBX","RSP","RBP","RSI","RDI","R8","R9","R10","R11","R12","R13","R14","R15"]

function (regfps) regfp_base ((base) b) =
  switch b {
    case NoBase -> [|| ||]
    case RipBase -> [|| RFull("RIP") ||]
    case (RegBase(b)) -> [|| RFull(GPRstr[b]) ||]
  }

function (regfps) regfp_idx ((option<scale_index>) idx) =
  switch idx {
    case (None) -> [|| ||]
    case (Some(scale, idx)) -> [|| RFull(GPRstr[idx]) ||]
  }

function (bool, regfps, regfps) regfp_rm ((rm) r) =
  switch r {
    case (Reg(n)) -> 
       (false, [|| RFull(GPRstr[n]) ||], [|| ||])
    case (Mem(idx, b, d)) -> {
       (true, [|| ||], append(regfp_idx(idx), regfp_base(b)))
    }
  }

function (instruction_kind, regfps, regfps, regfps) regfp_dest_src ((dest_src) ds) =
  switch ds {
    case (Rm_i (r_m, i)) ->
      let (m,rd,ars) = regfp_rm(r_m) in
      (if m then IK_mem_write(Write_plain) else IK_simple, ars, rd, ars)
    case (Rm_r (r_m, r)) ->
      let (m,rd,ars) = regfp_rm(r_m) in
      (if m then IK_mem_write(Write_plain) else IK_simple, RFull(GPRstr[r]) :: ars, rd, ars)
    case (R_rm (r, r_m)) ->
      let (m,rs,ars) = regfp_rm(r_m) in
      (if m then IK_mem_read(Read_plain) else IK_simple, append(rs, ars), [|| RFull(GPRstr[r]) ||], ars)
  }

(* as above but where destination is also a source operand *)
function (instruction_kind, regfps, regfps, regfps) regfp_dest_src_rmw ((dest_src) ds) =
  switch ds {
    case (Rm_i (r_m, i)) ->
      let (m,rds, ars) = regfp_rm(r_m) in
      (if m then IK_mem_rmw(Read_plain, Write_plain) else IK_simple, append(rds, ars), rds, ars)
    case (Rm_r (r_m, r)) ->
      let (m,rds, ars) = regfp_rm(r_m) in
      (if m then IK_mem_rmw(Read_plain, Write_plain) else IK_simple, RFull(GPRstr[r]) :: append(rds, ars), rds, ars)
    case (R_rm (r, r_m)) ->
      let rds = [|| RFull(GPRstr[r]) ||] in
      let (m,rs,ars) = regfp_rm(r_m) in
      (if m then IK_mem_read(Read_plain) else IK_simple, append(rds, ars), rds, ars)
  }

function (bool, regfps, regfps) regfp_imm_rm ((imm_rm) i_rm) =
  switch i_rm {
    case (Rm (v)) -> regfp_rm (v)
    case (Imm (v)) -> (false, [|| ||], [|| ||])
  }

let all_flags_but_cf_of = [|| RFull("AF"), RFull("PF"), RFull("SF"), RFull("ZF") ||]
let all_flags = append([|| RFull("CF"), RFull("OF") ||], all_flags_but_cf_of)

function (regfps) regfp_binop_flags ((binop_name) op) = 
  switch (op) {
    case Add -> all_flags
    case Sub -> all_flags
    case Cmp -> all_flags
    case Test -> all_flags_but_cf_of
    case And -> all_flags_but_cf_of
    case Xor -> all_flags_but_cf_of
    case Or  -> all_flags_but_cf_of
    case Rol -> all_flags
    case Ror -> all_flags
    case Sar -> all_flags
    case Shl -> all_flags
    case Shr -> all_flags
    case Adc -> all_flags
    case Sbb -> all_flags
  }
function (regfps) regfp_cond ((cond) c) =
  switch c {
    case A  -> [|| RFull("CF"), RFull("ZF") ||]
    case NB -> [|| RFull("CF") ||]
    case B  -> [|| RFull("CF") ||]
    case NA -> [|| RFull("CF"), RFull("ZF") ||]
    case E  -> [|| RFull("ZF") ||]
    case G  -> [|| RFull("ZF"), RFull("SF"), RFull("OF") ||]
    case NL -> [|| RFull("SF"), RFull("OF") ||]
    case L  -> [|| RFull("SF"), RFull("OF") ||]
    case NG -> [|| RFull("ZF"), RFull("SF"), RFull("OF") ||]
    case NE -> [|| RFull("ZF") ||]
    case NO -> [|| RFull("OF") ||]
    case NP -> [|| RFull("PF") ||]
    case NS -> [|| RFull("SF") ||]
    case O  -> [|| RFull("OF") ||]
    case P  -> [|| RFull("PF") ||]
    case S  -> [|| RFull("SF") ||]
    case ALWAYS -> [|| ||]
  }

function (regfps,regfps,regfps,niafps,diafp,instruction_kind) initial_analysis (instr) = {
  iR := [|| ||];
  oR := [|| ||];
  aR := [|| ||];
  ik := IK_simple;
  Nias := [|| NIAFP_successor ||];
  Dia := DIAFP_none;
  x := (qword) RIP;
  switch instr {
    case(Binop   (binop, sz, ds)) -> {
      let flags = regfp_binop_flags (binop) in
      let (ik', iRs, oRs, aRs) = regfp_dest_src_rmw(ds) in {
        ik := ik';
        iR := append(iRs, iR);
        oR := append(flags, append(oRs, oR));
        aR := append(aRs, aR);
      }
    }
    (*case(CALL    (imm_rm)             ) -> {

    }*)
    case(CLC                          ) -> oR := RFull("CF") :: oR
    case(CMC                          ) -> {
      iR := RFull("CF") :: iR;
      oR := RFull("CF") :: oR;
    }
    case(CMPXCHG (sz, r_m, reg)       ) ->
      let (m, rs, aRs) = regfp_rm (r_m) in {
        iK := if m then IK_mem_rmw (Read_plain, Write_plain) else IK_simple;
        iR := RFull("RAX") :: RFull(GPRstr[reg]) :: append(rs, aRs);
        oR := RFull("RAX") :: append(regfp_binop_flags(Cmp),  rs);
        aR := aRs;
      }
    case(DIV    (sz, r_m)             ) ->
      let (m, rs, ars) = regfp_rm (r_m) in {
        iK := if m then IK_mem_read (Read_plain) else IK_simple;
        iR := RFull("RAX") :: RFull("RDX") :: append(rs, ars);
        oR := RFull("RAX") :: RFull("RDX") :: append(oR, all_flags);
        aR := ars;
      }
    case(HLT                          ) -> ()
    (*case(Jcc     (cond, imm64)        ) -> `X86JCC     (translate_out_cond cond, translate_out_imm64 imm64)
    case(JMP     (rm)                 ) -> `X86JMP     (translate_out_rm rm)*)
    case(LEA     (sz, ds)             ) ->
      let (_, irs, ors, ars) = regfp_dest_src (ds) in {
        iR := irs;
        oR := ors;
        aR := ars;
      }
    (*case(LEAVE                        ) -> `X86LEAVE*)
    (*case(LOOP    (cond, imm64)        ) -> `X86LOOP    (translate_out_cond cond, translate_out_imm64 imm64)*)
    case(MFENCE                       ) -> iK := IK_barrier (Barrier_x86_MFENCE)
    case(Monop   (monop, sz, r_m)     ) -> 
      let (m, rds, ars) = regfp_rm(r_m) in {
        iK := if m then IK_mem_rmw(Read_plain, Write_plain) else IK_simple;
        iR := append(rds, ars);
        oR := append(all_flags_but_cf_of, rds); (* XXX fix flags *)
        aR := ars;
      }
    case(MOV     (c, sz, ds) )       -> 
      let (ik, irs, ors, ars) = regfp_dest_src (ds) in 
      let flags = regfp_cond(c) in
      {
          iK := ik;
          iR := append(irs, flags);
          oR := ors;
          aR := ars;
      }
    case(MOVSX   (sz1, ds, sz2) ) -> 
      let (ik, irs, ors, ars) = regfp_dest_src (ds) in {
          iK := ik;
          iR := irs;
          oR := ors;
          aR := ars;
      }
    case(MOVZX   (sz1, ds, sz2) ) -> 
      let (ik, irs, ors, ars) = regfp_dest_src (ds) in {
          iK := ik;
          iR := irs;
          oR := ors;
          aR := ars;
      }
    case(MUL    (sz, r_m)              ) ->
      let (m, rs, ars) = regfp_rm (r_m) in {
        iK := if m then IK_mem_read (Read_plain) else IK_simple;
        iR := RFull("RAX") :: append(rs, ars);
        oR := RFull("RAX") :: RFull("RDX") :: append(oR, all_flags);
        aR := ars;
      }
    case(NOP     (_)                  ) -> ()
    case(POP     (r_m)                ) -> 
      let (m, rd, ars) = regfp_rm (r_m) in {
        iK := if m then IK_mem_rmw(Read_plain, Write_plain) else IK_mem_write(Write_plain);
        iR := RFull("RSP") :: ars;
        oR := RFull("RSP") :: rd;
        aR := RFull("RSP") :: ars;
      }
    case(PUSH    (irm)               ) -> 
      let (m, rs, ars) = regfp_imm_rm (irm) in {
        iK := if m then IK_mem_rmw(Read_plain, Write_plain) else IK_mem_write(Write_plain);
        iR := RFull("RSP") :: append(rs, ars);
        oR := RFull("RSP") :: oR;
        aR := RFull("RSP") :: ars;
      }
    (*case(RET     (imm64)              ) -> `X86RET     (translate_out_imm64 imm64)*)
    case(SET     (c, b, r_m)          ) -> 
      let flags = regfp_cond(c) in
      let (m, rs, ars) = regfp_rm(r_m) in {
        iK := if m then IK_mem_write(Write_plain) else IK_simple;
        iR := append(flags, ars);
        oR := rs;
        aR := ars;
      }
    case(STC                          ) -> oR := [|| RFull("CF") ||]
    case(XADD    (sz, r_m, reg)       ) -> 
      let (m, rs, ars) = regfp_rm(r_m) in {
        iK := if m then IK_mem_rmw(Read_plain, Write_plain) else IK_simple;
        iR := RFull(GPRstr[reg]) :: append(rs, ars);
        oR := RFull(GPRstr[reg]) :: append(rs, all_flags);
        aR := ars;
      }
    case(XCHG    (sz, r_m, reg)       ) -> 
      let (m, rs, ars) = regfp_rm(r_m) in {
        iK := if m then IK_mem_rmw(Read_plain, Write_plain) else IK_simple;
        iR := RFull(GPRstr[reg]) :: append(rs, ars);
        oR := RFull(GPRstr[reg]) :: rs;
        aR := ars;
      }
  };
  (iR,oR,aR,Nias,Dia,ik)
}
