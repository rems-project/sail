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
$include <emulator_memory.sail>

$target_set emulator_prover c ocaml interpreter lem coq
$target_set emulator c isla ocaml interpreter
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

union Access_kind('arch_ak : Type) = {
  AK_explicit: Explicit_access_kind,
  AK_ifetch : unit, // Instruction fetch
  AK_ttw : unit, // Translation table walk
  AK_arch : 'arch_ak // Architecture specific type of access.
}

struct Mem_read_request('n : Int, 'vasize : Int, 'pa : Type, 'ts : Type,
                        'arch_ak: Type), 'n > 0 = {
  access_kind : Access_kind('arch_ak),
  // There may not always be a virtual address, e.g. when translation is off.
  // Additionally, translate reads don't have a (VA, PA) pair in the
  // translation relation anyway.
  va : option(bits('vasize)),
  pa : 'pa,
  translation : 'ts,
  size : int('n),
  tag : bool
}

val mem_read_request_is_exclusive : forall 'n 'vasize ('pa 'translation_summary 'arch_ak : Type), 'n > 0 & 'vasize > 0.
  Mem_read_request('n, 'vasize, 'pa, 'translation_summary, 'arch_ak) -> bool

function mem_read_request_is_exclusive(request) = {
    match request.access_kind {
        AK_explicit(eak) => match eak.variety {
            AV_exclusive => true,
            _ => false,
        },
        _ => false,
    }
}

val mem_read_request_is_ifetch : forall 'n 'vasize ('pa 'translation_summary 'arch_ak : Type), 'n > 0 & 'vasize > 0.
  Mem_read_request('n, 'vasize, 'pa, 'translation_summary, 'arch_ak) -> bool

function mem_read_request_is_ifetch(request) = {
    match request.access_kind {
        AK_ifetch() => true,
        _ => false,
    }
}

outcome sail_mem_read : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
  Mem_read_request('n, 'vasize, 'pa, 'translation_summary, 'arch_ak)
      -> result((bits(8 * 'n), option(bool)), 'abort)
with
  'pa : Type,
  'translation_summary : Type,
  'arch_ak : Type,
  'abort : Type
= {
    val pa_bits : 'pa -> {'pasize, 'pasize in {32, 64}. bits('pasize)}

    impl emulator(request) = {
        let pa = pa_bits(request.pa);
        let tag: option(bool) = if request.tag then {
            if length(pa) == 32 then {
                Some(read_tag#(32, pa))
            } else {
                Some(read_tag#(64, pa))
            }
        } else {
            None()
        };
        if mem_read_request_is_exclusive(request) then {
            if length(pa) == 32 then {
                Ok((read_mem_exclusive#(request, 32, pa, request.size), tag))
            } else {
                Ok((read_mem_exclusive#(request, 64, pa, request.size), tag))
            }
        } else if mem_read_request_is_ifetch(request) then {
            if length(pa) == 32 then {
                Ok((read_mem_ifetch#(request, 32, pa, request.size), tag))
            } else {
                Ok((read_mem_ifetch#(request, 64, pa, request.size), tag))
            }
        } else {
            if length(pa) == 32 then {
                Ok((read_mem#(request, 32, pa, request.size), tag))
            } else {
                Ok((read_mem#(request, 64, pa, request.size), tag))
            }
        }
    }
}

struct Mem_write_request('n : Int, 'vasize : Int, 'pa : Type, 'ts : Type,
                         'arch_ak : Type), 'n > 0 = {
  access_kind : Access_kind('arch_ak),
  va : option(bits('vasize)),
  pa : 'pa,          
  translation : 'ts,
  size : int('n),
  value : option(bits(8 * 'n)),
  tag : option(bool),
}

val mem_write_request_is_exclusive : forall 'n 'vasize ('pa 'translation_summary 'arch_ak : Type), 'n > 0 & 'vasize > 0.
  Mem_write_request('n, 'vasize, 'pa, 'translation_summary, 'arch_ak) -> bool

function mem_write_request_is_exclusive(request) = {
    match request.access_kind {
        AK_explicit(eak) => match eak.variety {
            AV_exclusive => true,
            _ => false,
        },
        _ => false,
    }
}

// the bool in the result is for the success/failure of a write-exclusive or a CAS, i.e.
outcome sail_mem_write_request : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
  Mem_write_request('n, 'vasize, 'pa, 'translation_summary, 'arch_ak)
      -> result(option(bool), 'abort)
with
  'pa : Type,
  'translation_summary : Type,
  'arch_ak : Type,
  'write_kind : Type,
  'abort : Type
= {
    val pa_bits : 'pa -> {'pasize, 'pasize in {32, 64}. bits('pasize)}

    impl emulator(request) = {
        let pa = pa_bits(request.pa);
        let b: bool = match request.value {
            Some(value) => if mem_write_request_is_exclusive(request) then {
                if length(pa) == 32 then {
                    write_mem_exclusive#(request, 32, pa, request.size, value)
                } else {
                    write_mem_exclusive#(request, 64, pa, request.size, value)
                }
            } else {
                if length(pa) == 32 then {
                    write_mem#(request, 32, pa, request.size, value)
                } else {
                    write_mem#(request, 64, pa, request.size, value)
                }
            },
            None() => true
        };
        match request.tag {
            Some(tag) => if length(pa) == 32 then {
                write_tag#(32, pa, tag)
            } else {
                write_tag#(64, pa, tag)
            },
            None() => ()
        };
        Ok(Some(b))
    }
}

$endif
