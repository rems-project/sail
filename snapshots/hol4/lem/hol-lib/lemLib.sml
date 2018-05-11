(*========================================================================*)
(*                        Lem                                             *)
(*                                                                        *)
(*          Dominic Mulligan, University of Cambridge                     *)
(*          Francesco Zappa Nardelli, INRIA Paris-Rocquencourt            *)
(*          Gabriel Kerneis, University of Cambridge                      *)
(*          Kathy Gray, University of Cambridge                           *)
(*          Peter Boehm, University of Cambridge (while working on Lem)   *)
(*          Peter Sewell, University of Cambridge                         *)
(*          Scott Owens, University of Kent                               *)
(*          Thomas Tuerk, University of Cambridge                         *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2013                               *)
(*  by the UK authors above and Institut National de Recherche en         *)
(*  Informatique et en Automatique (INRIA).                               *)
(*                                                                        *)
(*  All files except ocaml-lib/pmap.{ml,mli} and ocaml-libpset.{ml,mli}   *)
(*  are distributed under the license below.  The former are distributed  *)
(*  under the LGPLv2, as in the LICENSE file.                             *)
(*                                                                        *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(*========================================================================*)


structure lemLib =
struct

open HolKernel Parse boolLib bossLib;
open lemTheory intReduce wordsLib;

val run_interactive = ref false
val lem_conv_eval = computeLib.EVAL_CONV
val lem_conv_simp = SIMP_CONV (srw_ss()++permLib.PERM_ss) [] 


val lem_convs = [lem_conv_eval, lem_conv_simp];


datatype test_result =
    Success
  | Fail
  | Unknown of term


fun lem_run_single_test (t:term) conv = 
case total conv t of
    NONE => NONE
  | SOME thm => 
      if (can EQT_ELIM thm) then SOME Success else
      if (can EQF_ELIM thm) then SOME Fail else
      NONE
;

fun lem_run_test t = 
  case Lib.get_first (lem_run_single_test t) lem_convs of
      NONE => Unknown (rhs (concl (EVAL t)))
    | SOME r => r


fun lem_assertion s t =
let
    open PPBackEnd Parse;
    fun terminal_print sty s = (if !run_interactive then print_with_style sty s else
      Lib.with_flag (Parse.current_backend, PPBackEnd.vt100_terminal) (print_with_style sty) s);
    val _ = print "Testing ";
    val _ = terminal_print [FG LightBlue] s;
    val _ = print ": ``";
    val _ = print_term t;
    val _ = print ("`` ");
    val result = lem_run_test t;
    val _ = case result of
                Success => terminal_print [FG Green] "OK\n"
              | Fail => (terminal_print [FG OrangeRed] "FAILED\n";
                         if (not (!run_interactive)) then Process.exit Process.failure else ())
              | Unknown t => (terminal_print [FG Yellow] "evaluation failed\n")
(*                            print_term t;
                              print "\n\n"*) 
in
    ()
end;

end
