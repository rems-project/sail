/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/*  Sail and the Sail architecture models here, comprising all files and    */
/*  directories except the ASL-derived Sail code in the aarch64 directory,  */
/*  are subject to the BSD two-clause licence below.                        */
/*                                                                          */
/*  The ASL derived parts of the ARMv8.3 specification in                   */
/*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               */
/*                                                                          */
/*  Copyright (c) 2013-2021                                                 */
/*    Kathyrn Gray                                                          */
/*    Shaked Flur                                                           */
/*    Stephen Kell                                                          */
/*    Gabriel Kerneis                                                       */
/*    Robert Norton-Wright                                                  */
/*    Christopher Pulte                                                     */
/*    Peter Sewell                                                          */
/*    Alasdair Armstrong                                                    */
/*    Brian Campbell                                                        */
/*    Thomas Bauereiss                                                      */
/*    Anthony Fox                                                           */
/*    Jon French                                                            */
/*    Dominic Mulligan                                                      */
/*    Stephen Kell                                                          */
/*    Mark Wassell                                                          */
/*    Alastair Reid (Arm Ltd)                                               */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  This work was partially supported by EPSRC grant EP/K008528/1 <a        */
/*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          */
/*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   */
/*  KTF funding, and donations from Arm.  This project has received         */
/*  funding from the European Research Council (ERC) under the European     */
/*  Union’s Horizon 2020 research and innovation programme (grant           */
/*  agreement No 789108, ELVER).                                            */
/*                                                                          */
/*  This software was developed by SRI International and the University of  */
/*  Cambridge Computer Laboratory (Department of Computer Science and       */
/*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        */
/*  and FA8750-10-C-0237 ("CTSRD").                                         */
/*                                                                          */
/*  Redistribution and use in source and binary forms, with or without      */
/*  modification, are permitted provided that the following conditions      */
/*  are met:                                                                */
/*  1. Redistributions of source code must retain the above copyright       */
/*     notice, this list of conditions and the following disclaimer.        */
/*  2. Redistributions in binary form must reproduce the above copyright    */
/*     notice, this list of conditions and the following disclaimer in      */
/*     the documentation and/or other materials provided with the           */
/*     distribution.                                                        */
/*                                                                          */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      */
/*  SUCH DAMAGE.                                                            */
/*==========================================================================*/

$sail_internal

$ifndef _CONCURRENCY_INTERFACE
$define _CONCURRENCY_INTERFACE

$ifdef _DEFAULT_DEC
$include <vector_dec.sail>
$else
$include <vector_inc.sail>
$endif

$include <option.sail>

enum Access_variety = {
  AV_plain,
  AV_exclusive,
  AV_atomicRMW
}

enum Access_strength = {
  AS_normal,
  AS_Rel_or_Acq,
  AS_AcqRCpc
}

struct Explicit_access_kind = {
  EAK_variety : Access_variety,
  EAK_strength : Access_strength
}

union Access_kind = {
  AK_explicit: Explicit_access_kind,
  AK_ifetch : unit,
  AK_TTW : unit // Question: do we need to distinguish access-flag and dirty-bit writes?
}

enum Mem_external_sync_abort = {  
  MESA_Fault_SyncExternal,
  MESA_Fault_SyncParity,
  MESA_Fault_SyncExternalOnWalk,
  MESA_Fault_SyncParityOnWalk
}

union Mem_result('a: Type) = {
  MR_value : 'a,
  MR_abort : Mem_external_sync_abort
}

struct Mem_read_request('n : Int, 'vasize : Int, 'pa : Type, 'ts : Type) = {
  MR_access_kind : Access_kind,
  // There may not always be a virtual address, e.g. when translation is off.
  // Additionally, translate reads don't have a (VA, PA) pair in the
  // translation relation anyway.
  MR_VA : option(bits('vasize)),  
  MR_PA : 'pa,  // not sure if nicer to include addrs here, or in Translation?  Mostly the memory model deals in PAs, and often, so here?
  MR_translation : 'ts,
  MR_size : int('n),
  MR_tag : bool
}

val __read_tag = "read_tag_bool"  : bits(64) -> bool effect {rmem}

event __mem_read_request : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
  Mem_read_request('n, 'vasize, 'pa, 'translation_summary) -> Mem_result((bits(8 * 'n), option(bool))) effect {rmem}
with
  'pa : Type,
  'translation_summary : Type,
  'read_kind : Type
= {
  val pa_bits : 'pa -> {'pasize, 'pasize in {32, 64}. bits('pasize)}

  val request_read_kind : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
    Mem_read_request('n, 'vasize, 'pa, 'translation_summary) -> 'read_kind

  val platform_read_mem : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
    ('read_kind, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n) effect {rmem}

  impl c(request) = {
    let pa = pa_bits(request.MR_PA);
    let rk = request_read_kind(request);
    let tag: option(bool) = if request.MR_tag then {
        Some(__read_tag(sail_zero_extend(pa, 64)))
    } else {
        None()
    };
    if length(pa) == 32 then {
      MR_value((platform_read_mem(rk, 32, pa, request.MR_size), tag))
    } else {
      MR_value((platform_read_mem(rk, 64, pa, request.MR_size), tag))
    }
  }
}

struct Mem_write_request('n : Int, 'vasize : Int, 'pa : Type, 'ts : Type) = {
  MW_access_kind : Access_kind,
  MW_VA : option(bits('vasize)),
  MW_PA : 'pa,          
  MW_translation : 'ts,
  MW_size : int('n),
  MW_value : bits(8 * 'n),
  MW_tag : option(bool),
}

val __write_tag = "write_tag_bool" : (bits(64), bool) -> unit effect {wmv}

// the bool in the result is for the success/failure of a write-exclusive or a CAS
event __mem_write_request : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
  Mem_write_request('n, 'vasize, 'pa, 'translation_summary) -> Mem_result(option(bool)) effect {wmv}
with
  'pa : Type,
  'translation_summary : Type,
  'write_kind : Type
= {
  val pa_bits : 'pa -> {'pasize, 'pasize in {32, 64}. bits('pasize)}

  val request_write_kind : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
    Mem_write_request('n, 'vasize, 'pa, 'translation_summary) -> 'write_kind

  val platform_write_mem : forall 'n (constant 'addrsize : Int), 'n > 0 & 'addrsize in {32, 64}.
    ('write_kind, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool effect {wmv}

  impl c(request) = {
    let pa = pa_bits(request.MW_PA);
    let wk = request_write_kind(request);
    if length(pa) == 32 then {
      let _ = platform_write_mem(wk, 32, pa, request.MW_size, request.MW_value);
      ()
    } else {
      let _ = platform_write_mem(wk, 64, pa, request.MW_size, request.MW_value);
      ()
    };
    match request.MW_tag {
      Some(tag) => __write_tag(sail_zero_extend(pa, 64), tag),
      None() => ()
    };
    MR_value(None())
  }
}

// Announce an imminent write, at the given address and with the  given size,
// when those become available (maybe before the data becomes available).

struct Mem_write_announce_address('n : Int, 'vasize : Int, 'pa : Type) = {
  MWAA_PA : 'pa,          
  MWAA_size : int('n)
}

event __mem_write_announce_address : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
  Mem_write_announce_address('n, 'vasize, 'pa) -> unit  effect {wmem}
with
  'pa : Type

// Announce an imminent branch, to the given address

event __branch_announce_address : 'pa -> unit
with
  'pa : Type
= {
  val pa_bits : 'pa -> {'pasize, 'pasize in {32, 64}. bits('pasize)}

  val platform_branch_announce : forall (constant 'addrsize : Int), 'addrsize in {32, 64}.
    (int('addrsize), bits('addrsize)) -> unit

  impl c(pa) = {
    let pa = pa_bits(pa);
    if length(pa) == 32 then {
      platform_branch_announce(32, pa)
    } else {
      platform_branch_announce(64, pa)
    }
  }
}

event __barrier_request : 'barrier -> unit effect {barr}
with
  'barrier : Type,
  'barrier_kind : Type
= {
  val barrier_kind : 'barrier -> 'barrier_kind

  val platform_barrier : 'barrier_kind -> unit effect {barr}

  impl c(barrier) = platform_barrier(barrier_kind(barrier))
}

event __cache_op_request : 'cache_op -> unit
with
  'cache_op : Type,
  'cache_op_kind : Type
= {
  val request_cache_op_kind : 'cache_op -> 'cache_op_kind

  val request_addr : 'cache_op -> {'pasize, 'pasize in {32, 64}. bits('pasize)}

  val platform_cache_maintenance : forall (constant 'addrsize : Int), 'addrsize in {32, 64}.
    ('cache_op_kind, int('addrsize), bits('addrsize)) -> unit

  impl c(request) = {
    let pa = request_addr(request);
    let kind = request_cache_op_kind(request);
    if length(pa) == 32 then {
      platform_cache_maintenance(kind, 32, pa)
    } else {
      platform_cache_maintenance(kind, 64, pa)
    }
  }
}

event __tlb_op_request : 'tlb_op -> unit
with
  'tlb_op : Type,
  'cache_op_kind : Type
= {
  val request_cache_op_kind : 'tlb_op -> 'cache_op_kind

  val request_encode : 'tlb_op -> bits(64)

  val platform_cache_maintenance_extra : forall (constant 'addrsize : Int), 'addrsize in {32, 64}.
    ('cache_op_kind, int('addrsize), bits('addrsize), bits(64)) -> unit

  impl c(request) = {
    platform_cache_maintenance_extra(request_cache_op_kind(request), 64, sail_zeros(64), request_encode(request))
  }
}

event __fault : 'fault -> unit with 'fault : Type

event __exception_return : 'pa -> unit with 'pa : Type

val __instr_announce
  = { ocaml: "Platform.instr_announce", c: "platform_instr_announce", _: "instr_announce" }
  : forall 'n, 'n > 0.
  bits('n) -> unit

$endif
