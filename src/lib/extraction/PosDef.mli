open BinNums
open Datatypes

module Pos :
 sig
  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison
 end
