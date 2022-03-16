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
$include <result.sail>
$include <isla.sail>

$target_set emulator_prover c ocaml interpreter lem coq
$target_set emulator c ocaml interpreter
$target_set prover lem coq

enum Access_variety = {
  AV_plain,
  AV_exclusive,
  AV_atomic_rmw
}

enum Access_strength = {
  AS_normal,
  AS_rel_or_acq, // Release or acquire
  AS_acq_rcpc // Release-consistency with processor consistency
}

struct Explicit_access_kind = {
  variety : Access_variety,
  strength : Access_strength
}

union Access_kind = {
  AK_explicit: Explicit_access_kind,
  AK_ifetch : unit, // Instruction fetch
  AK_ttw : unit // Translation table walk
}

struct Mem_read_request('n : Int, 'vasize : Int, 'pa : Type, 'ts : Type), 'n > 0 = {
  access_kind : Access_kind,
  // There may not always be a virtual address, e.g. when translation is off.
  // Additionally, translate reads don't have a (VA, PA) pair in the
  // translation relation anyway.
  va : option(bits('vasize)),  
  pa : 'pa,
  translation : 'ts,
  size : int('n),
  tag : bool
}

val __read_tag# = monadic "read_tag_bool"  : bits(64) -> bool

val bit_to_bool : bit -> bool
function bit_to_bool b = match b {
  bitone  => true,
  bitzero => false
}

outcome sail_mem_read_request : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
  Mem_read_request('n, 'vasize, 'pa, 'translation_summary) -> result((bits(8 * 'n), option(bool)), 'abort)
with
  'pa : Type,
  'translation_summary : Type,
  'read_kind : Type,
  'abort : Type
= {
  val pa_bits : 'pa -> {'pasize, 'pasize in {32, 64}. bits('pasize)}

  val request_read_kind : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
    Mem_read_request('n, 'vasize, 'pa, 'translation_summary) -> 'read_kind

  val platform_read_mem : forall 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    ('read_kind, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

  val platform_read_memt : forall 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    ('read_kind, bits('addrsize), int('n)) -> (bits(8 * 'n), bit)

  impl prover(request) = {
    let pa = pa_bits(request.pa);
    let rk = request_read_kind(request);
    if request.tag then {
      let (data, tag) = platform_read_memt(rk, pa, request.size);
      Ok((data, Some(bit_to_bool(tag))))
    } else {
      Ok((platform_read_mem(rk, length(pa), pa, request.size), None()))
    }
  }

  impl emulator(request) = {
    let pa = pa_bits(request.pa);
    let rk = request_read_kind(request);
    let tag: option(bool) = if request.tag then {
        Some(__read_tag#(sail_zero_extend(pa, 64)))
    } else {
        None()
    };
    if length(pa) == 32 then {
      Ok((platform_read_mem(rk, 32, pa, request.size), tag))
    } else {
      Ok((platform_read_mem(rk, 64, pa, request.size), tag))
    }
  }
}

struct Mem_write_request('n : Int, 'vasize : Int, 'pa : Type, 'ts : Type), 'n > 0 = {
  access_kind : Access_kind,
  va : option(bits('vasize)),
  pa : 'pa,          
  translation : 'ts,
  size : int('n),
  value : option(bits(8 * 'n)),
  tag : option(bool),
}

val __write_tag# = "write_tag_bool" : (bits(64), bool) -> unit

// the bool in the result is for the success/failure of a write-exclusive or a CAS, i.e.
outcome sail_mem_write_request : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
  Mem_write_request('n, 'vasize, 'pa, 'translation_summary) -> result(option(bool), 'abort)
with
  'pa : Type,
  'translation_summary : Type,
  'write_kind : Type,
  'abort : Type
= {
  val pa_bits : 'pa -> {'pasize, 'pasize in {32, 64}. bits('pasize)}

  val request_write_kind : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
    Mem_write_request('n, 'vasize, 'pa, 'translation_summary) -> 'write_kind

  val platform_write_mem : forall 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    ('write_kind, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool

  impl emulator(request) = {
    let pa = pa_bits(request.pa);
    let wk = request_write_kind(request);
    let b: bool = match request.value {
      Some(value) => if length(pa) == 32 then {
        platform_write_mem(wk, 32, pa, request.size, value);
      } else {
        platform_write_mem(wk, 64, pa, request.size, value);
      },
      None() => true
    };
    match request.tag {
      Some(tag) => __write_tag#(sail_zero_extend(pa, 64), tag),
      None() => ()
    };
    Ok(Some(b))
  }
}

// Announce an imminent write, at the given address and with the  given size,
// when those become available (maybe before the data becomes available).
struct Mem_write_announce_address('n : Int, 'vasize : Int, 'pa : Type) = {
  pa : 'pa,          
  size : int('n)
}

outcome sail_mem_write_announce_address : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
  Mem_write_announce_address('n, 'vasize, 'pa) -> unit
with
  'pa : Type

// Announce an imminent branch, to the given address
outcome sail_branch_announce_address : 'pa -> unit
with
  'pa : Type
= {
  val pa_bits : 'pa -> {'pasize, 'pasize in {32, 64}. bits('pasize)}

  val platform_branch_announce : forall 'addrsize, 'addrsize in {32, 64}.
    (int('addrsize), bits('addrsize)) -> unit

  impl emulator(pa) = {
    let pa = pa_bits(pa);
    if length(pa) == 32 then {
      platform_branch_announce(32, pa)
    } else {
      platform_branch_announce(64, pa)
    }
  }
}

outcome sail_barrier_request : 'barrier -> unit
with
  'barrier : Type,
  'barrier_kind : Type
= {
  val barrier_kind : 'barrier -> 'barrier_kind

  val platform_barrier : 'barrier_kind -> unit

  impl emulator(barrier) = platform_barrier(barrier_kind(barrier))
}

outcome sail_cache_op_request : 'cache_op -> unit
with
  'cache_op : Type,
  'cache_op_kind : Type
= {
  val cache_op_kind : 'cache_op -> 'cache_op_kind

  val cache_op_addr : 'cache_op -> {'pasize, 'pasize in {32, 64}. bits('pasize)}

  val platform_cache_maintenance : forall 'addrsize, 'addrsize in {32, 64}.
    ('cache_op_kind, int('addrsize), bits('addrsize)) -> unit

  impl emulator(request) = {
    let pa = cache_op_addr(request);
    let kind = cache_op_kind(request);
    if length(pa) == 32 then {
      platform_cache_maintenance(kind, 32, pa)
    } else {
      platform_cache_maintenance(kind, 64, pa)
    }
  }
}

outcome sail_tlb_op_request : 'tlb_op -> unit
with
  'tlb_op : Type,
  'cache_op_kind : Type
= {
  val tlb_op_kind : 'tlb_op -> 'cache_op_kind

  val tlb_op_encode : 'tlb_op -> bits(64)

  val platform_cache_maintenance_extra : forall 'addrsize, 'addrsize in {32, 64}.
    ('cache_op_kind, int('addrsize), bits('addrsize), bits(64)) -> unit

  impl emulator(request) = {
    platform_cache_maintenance_extra(tlb_op_kind(request), 64, sail_zeros(64), tlb_op_encode(request))
  }

  impl isla(request) = {
    isla_log_event("tlb-op", request) 
  }
}

outcome sail_fault_announce : 'fault -> unit with 'fault : Type = {
  impl isla(fault) = {
    isla_log_event("fault", fault)
  }
}

outcome sail_eret_announce : 'pa -> unit with 'pa : Type = {
  impl isla(pa) = {
    isla_log_event("eret", pa)
  }
}

val sail_instr_announce
  = { ocaml: "Platform.instr_announce", c: "platform_instr_announce", _: "instr_announce" }
  : forall 'n, 'n > 0.
  bits('n) -> unit

$endif
