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
(*          Brian Campbell, University of Edinburgh                       *)
(*          Shaked Flur, University of Cambridge                          *)
(*          Thomas Bauereiss, University of Cambridge                     *)
(*          Stephen Kell, University of Cambridge                         *)
(*          Thomas Williams                                               *)
(*          Lars Hupel                                                    *)
(*          Basile Clement                                                *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2018                               *)
(*  by the authors above and Institut National de Recherche en            *)
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

chapter\<open>Mappings of Syntax needed by Lem\<close>

theory "Lem"

imports
         LemExtraDefs
         "HOL-Word.Word"
begin

type_synonym numeral = nat

subsection \<open>Finite Maps\<close>

abbreviation (input) "map_find k m \<equiv> the (m k)"
abbreviation (input) "map_update k v m \<equiv> m (k \<mapsto> v)"
abbreviation (input) "map_remove k m \<equiv> m |` (- {k})"
abbreviation (input) "map_any P m \<equiv> \<exists> (k, v) \<in> map_to_set m. P k v"
abbreviation (input) "map_all P m \<equiv> \<forall> (k, v) \<in> map_to_set m. P k v"

subsection \<open>Lists\<close>

abbreviation (input) "list_mem e l \<equiv> (e \<in> set l)"
abbreviation (input) "list_forall P l \<equiv> (\<forall>e\<in>set l. P e)"
abbreviation (input) "list_exists P l \<equiv> (\<exists>e\<in>set l. P e)"
abbreviation (input) "list_unzip l \<equiv> (map fst l, map snd l)"

subsection \<open>Sets\<close>

abbreviation (input) "set_filter P (s::'a set) \<equiv> {x \<in> s. P x}"
abbreviation (input) "set_bigunion S \<equiv> \<Union> S"
abbreviation (input) "set_biginter S \<equiv> \<Inter> S"

subsection \<open>Natural numbers\<close>

subsection \<open>Integers\<close>


subsection \<open>Dummy\<close>

consts
  bitwise_xor :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  num_asr :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  num_lsl :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  bitwise_or :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  bitwise_not :: "nat \<Rightarrow> nat"
  bitwise_and :: "nat \<Rightarrow> nat \<Rightarrow> nat"

subsection \<open>Machine words\<close>

definition word_update :: "'a::len word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'b::len word \<Rightarrow> 'a word" where
  "word_update v lo hi w =
    (let sz = size v in
    of_bl (take (sz-hi-1) (to_bl v) @ to_bl w @ drop (sz-lo) (to_bl v)))"

end
