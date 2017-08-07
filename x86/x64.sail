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

val extern forall Nat 'n. (bit['n],[|'n|]) -> bit['n] effect pure ASR
val extern forall Nat 'n. (bit['n],[|'n|]) -> bit['n] effect pure LSR
val extern forall Nat 'n. (bit['n],[|'n|]) -> bit['n] effect pure ROR
val extern forall Nat 'n. (bit['n],[|'n|]) -> bit['n] effect pure ROL
val cast bool -> bit effect pure cast_bool_bit
val cast bit -> int effect pure cast_bit_int
val extern forall Num 'n. int -> bit['n] effect pure cast_int_vec
val extern forall 'n, 'm, 'o, 'n <= 0, 'm <= 'o. [|'n:'m|] -> [|0:'o|] effect pure negative_to_zero

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

register bit CF
register bit PF
register bit AF
register bit ZF
register bit SF
register bit OF

(* --------------------------------------------------------------------------
   Memory
   -------------------------------------------------------------------------- *)

val extern forall Nat 'n. (qword, [|'n|]) -> (bit[8 * 'n]) effect { rmem } MEM

val extern forall Nat 'n. (qword, [|'n|], bit[8 * 'n]) -> unit effect { wmem } wMEM

(* --------------------------------------------------------------------------
   Helper functions
   -------------------------------------------------------------------------- *)

(* Instruction addressing modes *)

typedef size = const union {
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

typedef cond = enumerate {
  O; NO; B; NB; E; NE; NA; A; S; NS; P; NP; L; NL; NG; G; ALWAYS
}

(* Effective addresses *)

typedef ea = const union {
  (size,qword) Ea_i;
  (size,regn)  Ea_r;
  (size,qword) Ea_m;
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

function ea ea_rm ((size) sz, (rm) r) =
  switch r {
    case (Reg(n)) -> Ea_r (sz, n)
    case (Mem(idx, b, d)) -> Ea_m (sz, ea_index(idx) + (qword) (ea_base(b) + d))
  }

function ea ea_dest ((size) sz, (dest_src) ds) =
  switch ds {
    case (Rm_i (v, _)) -> ea_rm (sz, v)
    case (Rm_r (v, _)) -> ea_rm (sz, v)
    case (R_rm (v, _)) -> Ea_r (sz, v)
  }

function ea ea_src ((size) sz, (dest_src) ds) =
  switch ds {
    case (Rm_i (_, v)) -> Ea_i (sz, v)
    case (Rm_r (_, v)) -> Ea_r (sz, v)
    case (R_rm (_, v)) -> ea_rm (sz, v)
  }

function ea ea_imm_rm ((size) sz, (imm_rm) i_rm) =
  switch i_rm {
    case (Rm (v)) -> ea_rm (sz, v)
    case (Imm (v)) -> Ea_i (sz, v)
  }

function qword restrictSize ((size) sz, (qword) imm) =
  switch sz {
    case (Sz8(_)) -> imm & 0x00000000000000FF
    case Sz16     -> imm & 0x000000000000FFFF
    case Sz32     -> imm & 0x00000000FFFFFFFF
    case Sz64     -> imm
  }

function regn sub4 ((regn) r) = negative_to_zero (r - 4)

function qword effect { rreg, rmem } EA ((ea) e) =
  switch e {
    case (Ea_i(sz,i)) -> restrictSize(sz,i)
    case (Ea_r((Sz8(have_rex)),r)) ->
      if have_rex | r < 4 (* RSP *) | r > 7 (* RDI *) then
        REG[r]
      else
        LSR (REG[sub4 (r)], 8) & 0x00000000000000FF
    case (Ea_r(sz,r)) -> restrictSize(sz, REG[r])
    case (Ea_m((Sz8(_)),a)) -> EXTZ (MEM(a, 1))
    case (Ea_m(Sz16,a)) -> EXTZ (MEM(a, 2))
    case (Ea_m(Sz32,a)) -> EXTZ (MEM(a, 4))
    case (Ea_m(Sz64,a)) -> MEM(a, 8)
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
        regr[15 .. 8] := (vector<15,8,dec,bit>) (adjust_dec(w[7 .. 0]));
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

function (ea, qword, qword) read_dest_src_ea ((size) sz, (dest_src) ds) =
  let e = ea_dest (sz, ds) in
  (e, EA(e), EA(ea_src(sz, ds)))

function qword call_dest_from_ea ((ea) e) =
  switch e {
    case (Ea_i(_, i)) -> RIP + i
    case (Ea_r(_, r)) -> REG[r]
    case (Ea_m(_, a)) -> MEM(a, 8)
  }

function qword get_ea_address ((ea) e) =
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

function [|64|] size_width ((size) sz) =
  switch sz {
    case (Sz8(_)) -> 8
    case Sz16 -> 16
    case Sz32 -> 32
    case Sz64 -> 64
  }

function [|63|] size_width_sub1 ((size) sz) =
  switch sz {
    case (Sz8(_)) -> 7
    case Sz16 -> 15
    case Sz32 -> 31
    case Sz64 -> 63
  }

(* XXXXX
function bit word_size_msb ((size) sz, (qword) w) = w[size_width(sz) - 1]
*)

function bit word_size_msb ((size) sz, (qword) w) = w[size_width_sub1(sz)]

function unit write_PF ((qword) w) = PF := byte_parity (w[7 .. 0])

function unit write_SF ((size) sz, (qword) w) = SF := word_size_msb (sz, w)

function unit write_ZF ((size) sz, (qword) w) =
  ZF := (bit)
         (switch sz {
            case (Sz8(_)) -> w[7 .. 0] == 0x00
            case Sz16 -> w[15 .. 0] == 0x0000
            case Sz32 -> w[31 .. 0] == 0x00000000
            case Sz64 -> w == 0x0000000000000000
          })

function unit write_arith_eflags_except_CF_OF ((size) sz, (qword) w) =
{
  AF := undefined;
  write_PF(w);
  write_SF(sz, w);
  write_ZF(sz, w);
}

function unit write_arith_eflags ((size) sz, (qword) w, (bit) c, (bit) x) =
{
  CF := c;
  OF := x;
  write_arith_eflags_except_CF_OF (sz, w)
}

function unit write_logical_eflags ((size) sz, (qword) w) =
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

(* XXXXX *)
function nat power ((nat) x, ([|64|]) y) = undefined

function nat value_width ((size) sz) = power (2, size_width(sz))

function bit word_signed_overflow_add ((size) sz, (qword) a, (qword) b) =
  (bit) (word_size_msb (sz, a) == word_size_msb (sz, b) &
         word_size_msb (sz, a + b) != word_size_msb (sz, a))

function bit word_signed_overflow_sub ((size) sz, (qword) a, (qword) b) =
  (bit) (word_size_msb (sz, a) != word_size_msb (sz, b) &
         word_size_msb (sz, a - b) != word_size_msb (sz, a))

function (qword, bit, bit) add_with_carry_out ((size) sz, (qword) a, (qword) b) =
  (a + b, (bit) ((int) (value_width (sz)) <= unsigned(a) + unsigned(b)),
   word_signed_overflow_add (sz, a, b))

function (qword, bit, bit) sub_with_borrow ((size) sz, (qword) a, (qword) b) =
  (a - b, (bit) (a < b), word_signed_overflow_sub (sz, a, b))

function unit write_arith_result ((size) sz, (qword) w, (bit) c, (bit) x, (ea) e) =
{
  write_arith_eflags (sz, w, c, x);
  wEA (e) := w;
}

function unit write_arith_result_no_CF_OF ((size) sz, (qword) w, (ea) e) =
{
  write_arith_eflags_except_CF_OF (sz, w);
  wEA (e) := w;
}

function unit write_logical_result ((size) sz, (qword) w, (ea) e) =
{
  write_arith_eflags_except_CF_OF (sz, w);
  wEA (e) := w;
}

function unit write_result_erase_eflags ((qword) w, (ea) e) =
{
  erase_eflags ();
  wEA (e) := w;
}

function qword effect { escape } sign_extension ((qword) w, (size) size1, (size) size2) =
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

function [|64|] mask_shift ((size) sz, (qword) w) =
  if sz == Sz64 then w[5 .. 0] else w[4 .. 0]

function qword rol ((size) sz, (qword) a, (qword) b) =
  switch sz {
    case (Sz8(_)) -> EXTZ (ROL (a[7 .. 0], b[2 .. 0]))
    case Sz16 -> EXTZ (ROL (a[15 .. 0], b[3 .. 0]))
    case Sz32 -> EXTZ (ROL (a[31 .. 0], b[4 .. 0]))
    case Sz64 -> ROL (a, b[5 .. 0])
  }

function qword ror ((size) sz, (qword) a, (qword) b) =
  switch sz {
    case (Sz8(_)) -> EXTZ (ROR (a[7 .. 0], b[2 .. 0]))
    case Sz16 -> EXTZ (ROR (a[15 .. 0], b[3 .. 0]))
    case Sz32 -> EXTZ (ROR (a[31 .. 0], b[4 .. 0]))
    case Sz64 -> ROR (a, b[5 .. 0])
  }

function qword sar ((size) sz, (qword) a, (qword) b) =
  switch sz {
    case (Sz8(_)) -> EXTZ (ASR (a[7 .. 0], b[2 .. 0]))
    case Sz16 -> EXTZ (ASR (a[15 .. 0], b[3 .. 0]))
    case Sz32 -> EXTZ (ASR (a[31 .. 0], b[4 .. 0]))
    case Sz64 -> ASR (a, b[5 .. 0])
  }

function unit write_binop ((size) sz, (binop_name) bop, (qword) a, (qword) b, (ea) e) =
  switch bop {
    case Add -> let (w,c,x) = add_with_carry_out (sz, a, b) in
                write_arith_result (sz, w, c, x, e)
    case Sub -> let (w,c,x) = sub_with_borrow (sz, a, b) in
                write_arith_result (sz, w, c, x, e)
    case Cmp -> let (w,c,x) = sub_with_borrow (sz, a, b) in
                write_arith_eflags (sz, w, c, x)
    case Test -> write_logical_eflags (sz, a & b)
    case And -> write_logical_result (sz, a & b, e)
    case Xor -> write_logical_result (sz, a ^ b, e)
    case Or -> write_logical_result (sz, a | b, e)
    case Rol -> write_result_erase_eflags (rol (sz, a, b), e)
    case Ror -> write_result_erase_eflags (ror (sz, a, b), e)
    case Sar -> write_result_erase_eflags (sar (sz, a, b), e)
    case Shl -> write_result_erase_eflags (a << mask_shift (sz,b), e)
    case Shr -> write_result_erase_eflags (LSR (a, mask_shift (sz,b)), e)
    case Adc ->
      {
        let carry = CF in
        let (qword) result = a + (qword) (b + carry) in
        {
          CF := (bit) ((int) (value_width (sz)) <= unsigned(a) + unsigned(b));
          OF := undefined;
          write_arith_result_no_CF_OF (sz, result, e);
        }
      }
    case Sbb ->
      {
        let carry = CF in
        let (qword) result = a - (qword) (b + carry) in
        {
          CF := (bit) (unsigned(a) < unsigned(b) + (int) carry);
          OF := undefined;
          write_arith_result_no_CF_OF (sz, result, e);
        }
      }
    case _ -> exit ()
  }

function unit write_monop ((size) sz, (monop_name) mop, (qword) a, (ea) e) =
  switch mop {
    case Not -> wEA(e) := ~(a)
    case Dec -> write_arith_result_no_CF_OF (sz, a - 1, e)
    case Inc -> write_arith_result_no_CF_OF (sz, a + 1, e)
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
  let top = MEM(RSP, 8) in
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
function unit push ((imm_rm) i) = push_aux (EA (ea_imm_rm (Sz64, i)))
function unit push_rip () = push_aux (RIP)

function unit drop ((qword) i) = if i[7 ..0] != 0 then () else RSP := RSP + i

(* --------------------------------------------------------------------------
   Instructions
   -------------------------------------------------------------------------- *)

scattered function unit execute
scattered typedef ast = const union

val ast -> unit effect {escape, rmem, rreg, undef, wmem, wreg} execute

(* ==========================================================================
      Binop
   ========================================================================== *)

union ast member (binop_name,size,dest_src) Binop

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
  jump_to_ea (ea_imm_rm (Sz64, i))
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

union ast member (size,rm,regn) CMPXCHG

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

union ast member (size,rm) DIV

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
    wEA(eax) := cast_int_vec(q);
    wEA(edx) := cast_int_vec(m);
    erase_eflags();
  }

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

union ast member (size,dest_src) LEA

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
      Monop
   ========================================================================== *)

union ast member (monop_name,size,rm) Monop

function clause execute (Monop (mop,sz,r)) =
  let e = ea_rm (sz, r) in write_monop (sz, mop, EA(e), e)

(* ==========================================================================
      MOV
   ========================================================================== *)

union ast member (cond,size,dest_src) MOV

function clause execute (MOV (c,sz,ds)) =
  if read_cond (c) then
    let src = ea_src (sz, ds) in
    let dst = ea_dest (sz, ds) in
    wEA(dst) := EA(src)
  else ()

(* ==========================================================================
      MOVSX
   ========================================================================== *)

union ast member (size,dest_src,size) MOVSX

function clause execute (MOVSX (sz1,ds,sz2)) =
  let src = ea_src (sz1, ds) in
  let dst = ea_dest (sz2, ds) in
  wEA(dst) := sign_extension (EA(src), sz1, sz2)

(* ==========================================================================
      MOVZX
   ========================================================================== *)

union ast member (size,dest_src,size) MOVZX

function clause execute (MOVZX (sz1,ds,sz2)) =
  let src = ea_src (sz1, ds) in
  let dst = ea_dest (sz2, ds) in
  wEA(dst) := EA(src)

(* ==========================================================================
      MUL
   ========================================================================== *)

union ast member (size,rm) MUL

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
        wEA(edx) := (LSR (m, size_width(sz)))[63 .. 0]
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

union ast member (size,rm,regn) XADD

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

union ast member (size,rm,regn) XCHG

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
