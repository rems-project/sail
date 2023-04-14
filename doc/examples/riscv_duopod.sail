/*=======================================================================================*/
/*  RISCV Sail Model                                                                     */
/*                                                                                       */
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except for the snapshots of the Lem and Sail libraries                   */
/*  in the prover_snapshots directory (which include copies of their                     */
/*  licences), is subject to the BSD two-clause licence below.                           */
/*                                                                                       */
/*  Copyright (c) 2017-2021                                                              */
/*    Prashanth Mundkur                                                                  */
/*    Rishiyur S. Nikhil and Bluespec, Inc.                                              */
/*    Jon French                                                                         */
/*    Brian Campbell                                                                     */
/*    Robert Norton-Wright                                                               */
/*    Alasdair Armstrong                                                                 */
/*    Thomas Bauereiss                                                                   */
/*    Shaked Flur                                                                        */
/*    Christopher Pulte                                                                  */
/*    Peter Sewell                                                                       */
/*    Alexander Richardson                                                               */
/*    Hesham Almatary                                                                    */
/*    Jessica Clarke                                                                     */
/*    Microsoft, for contributions by Robert Norton-Wright and Nathaniel Wesley Filardo  */
/*    Peter Rugg                                                                         */
/*    Aril Computer Corp., for contributions by Scott Johnson                            */
/*                                                                                       */
/*  All rights reserved.                                                                 */
/*                                                                                       */
/*  This software was developed by the above within the Rigorous                         */
/*  Engineering of Mainstream Systems (REMS) project, partly funded by                   */
/*  EPSRC grant EP/K008528/1, at the Universities of Cambridge and                       */
/*  Edinburgh.                                                                           */
/*                                                                                       */
/*  This software was developed by SRI International and the University of               */
/*  Cambridge Computer Laboratory (Department of Computer Science and                    */
/*  Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and                 */
/*  under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA                 */
/*  SSITH research programme.                                                            */
/*                                                                                       */
/*  This project has received funding from the European Research Council                 */
/*  (ERC) under the European Union’s Horizon 2020 research and innovation                */
/*  programme (grant agreement 789108, ELVER).                                           */
/*                                                                                       */
/*                                                                                       */
/*  Redistribution and use in source and binary forms, with or without                   */
/*  modification, are permitted provided that the following conditions                   */
/*  are met:                                                                             */
/*  1. Redistributions of source code must retain the above copyright                    */
/*     notice, this list of conditions and the following disclaimer.                     */
/*  2. Redistributions in binary form must reproduce the above copyright                 */
/*     notice, this list of conditions and the following disclaimer in                   */
/*     the documentation and/or other materials provided with the                        */
/*     distribution.                                                                     */
/*                                                                                       */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''                   */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED                    */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A                      */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR                  */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,                         */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT                     */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF                     */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND                  */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,                   */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT                   */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF                   */
/*  SUCH DAMAGE.                                                                         */
/*=======================================================================================*/

$span start PREAMBLE

default Order dec
$include <prelude.sail>

$span end

val EXTS : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
val EXTZ : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)

function EXTS(m, v) = sail_sign_extend(v, m)
function EXTZ(m, v) = sail_zero_extend(v, m)

type xlen       : Int = 64
type xlen_bytes : Int = 8
type xlenbits         = bits(xlen)

type regbits = bits(5)

val zeros : forall 'n, 'n >= 0. int('n) -> bits('n)
function zeros n = replicate_bits(0b0, n)

/* Architectural state */

register PC : xlenbits
register nextPC : xlenbits

register Xs : vector(32, dec, xlenbits)

/* Getters and setters for X registers (special case for zeros register, x0) */
val rX : regbits -> xlenbits

function rX(r) =
  match r {
    0b00000 => EXTZ(0x0),
    _ => Xs[unsigned(r)]
  }

val wX : (regbits, xlenbits) -> unit

function wX(r, v) =
  if r != 0b00000 then {
     Xs[unsigned(r)] = v;
  }

overload X = {rX, wX}

/* Accessors for memory */
val MEMr = monadic { lem: "MEMr", coq: "MEMr", _ : "read_ram" } : forall 'n 'm, 'n >= 0.
   (int('m), int('n), bits('m), bits('m)) -> bits(8 * 'n)

val read_mem : forall 'n, 'n >= 0. (xlenbits, int('n)) -> bits(8 * 'n)
function read_mem(addr, width) =
    MEMr(sizeof(xlen), width, EXTZ(0x0), addr)

/* Instruction decode and execute */
enum iop = {RISCV_ADDI, RISCV_SLTI, RISCV_SLTIU, RISCV_XORI, RISCV_ORI, RISCV_ANDI}
scattered union ast

val decode : bits(32) -> option(ast)

val execute : ast -> unit

/* ****************************************************************** */

/* ADDI */

union clause ast = ITYPE : (bits(12), regbits, regbits, iop)

function clause decode imm : bits(12) @ rs1 : regbits @ 0b000 @ rd : regbits @ 0b0010011
  = Some(ITYPE(imm, rs1, rd, RISCV_ADDI))

function clause execute (ITYPE (imm, rs1, rd, RISCV_ADDI)) =
  let rs1_val = X(rs1) in
  let imm_ext : xlenbits = EXTS(imm) in
  let result = rs1_val + imm_ext in
  X(rd) = result

/* ****************************************************************** */

/* Load double */
union clause ast = LOAD : (bits(12), regbits, regbits)

function clause decode imm : bits(12) @ rs1 : regbits @ 0b011 @ rd : regbits @ 0b0000011
  = Some(LOAD(imm, rs1, rd))

function clause execute(LOAD(imm, rs1, rd)) =
    let addr : xlenbits = X(rs1) + EXTS(imm) in
    let result : xlenbits = read_mem(addr, sizeof(xlen_bytes)) in
    X(rd) = result

/* ****************************************************************** */

function clause decode _ = None()

// Otherwise Sail will complain about unmatched cases
function clause execute _ = ()
