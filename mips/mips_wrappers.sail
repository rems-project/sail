(*========================================================================*)
(*                                                                        *)
(*  Copyright (c) 2015-2016 Robert M. Norton                              *)
(*  Copyright (c) 2015-2016 Kathyrn Gray                                  *)
(*  All rights reserved.                                                  *)
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
(*     notice, this list of conditions and the following disclaimer in the  *)
(*     documentation and/or other materials provided with the distribution.  *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND  *)
(*  ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE  *)
(*  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR    *)
(*  PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS  *)
(*  BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR  *)
(*  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF  *)
(*  SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR       *)
(*  BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,  *)
(*  WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE  *)
(*  OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN  *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(*========================================================================*)

function unit effect {wmem} MEMw_wrapper(addr, size, data) = MEMw(addr, size, data)
function bool effect {wmem} MEMw_conditional_wrapper(addr, size, data) =
  MEMw_conditional(addr, size, data)

function bit[64] addrWrapper((bit[64]) addr, (MemAccessType) accessType, (WordType) width) =
    addr

function (bit[64]) TranslateAddress ((bit[64]) vAddr, (MemAccessType) accessType) = {
    incrementCP0Count();
    if (vAddr[1..0] != 0b00) then (* bad PC alignment *)
      exit (SignalExceptionBadAddr(AdEL, vAddr))
    else
      TLBTranslate(vAddr, accessType)
}

let have_cp2 = false

function unit SignalException ((Exception) ex) = SignalExceptionMIPS(ex)

function unit ERETHook() = ()
