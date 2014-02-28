(* XXX types are wrong *)
val extern forall Type 'a . ( 'a * 'a ) -> 'a effect pure (deinfix + ) = "add"
val extern forall Type 'a, Type 'b, Type 'c .
  ( 'a * 'b ) -> 'c effect pure (deinfix : ) = "vec_concat"
val extern forall Type 'a . 'a -> nat effect pure to_num_inc = "to_num_inc"
val extern forall Type 'a . 'a -> nat effect pure to_num_dec = "to_num_dec"
val extern forall Type 'a . nat -> 'a effect pure to_vec_inc = "to_vec_inc"
val extern forall Type 'a . nat -> 'a effect pure to_vec_dec = "to_vec_dec"

val extern forall Type 'a . ( 'a * 'a ) -> bit effect pure (deinfix == ) = "eq"
val extern forall Type 'a . ( 'a * 'a ) -> bit effect pure (deinfix != ) = "neq"

val extern bit -> bit effect pure (deinfix ~ ) = "bitwise-not"
val extern ( bit * bit ) -> bit effect pure (deinfix ^ ) = "bitwise-xor"
val extern ( bit * bit ) -> bit effect pure (deinfix & ) = "bitwise-and"

val extern bit -> bool effect pure is_one = "is_one"

(* XXX sign extension *)
function forall Type 'a . 'a exts ( x ) = x

register (vector<0, 16, inc, (vector<0, 63, inc, bit>)> ) GPR

register (bit[64]) NIA (* next instruction address *)
register (bit[64]) CIA (* current instruction address *)

(* XXX endianess; also, bit[64] translates to 0:64, not 0:63??? *)
register (bit[32 : 63]) CR
register (bit[64]) CTR
register (bit[64]) LR

val extern ( nat * nat ) -> (bit[64]) effect { wmem , rmem } MEM

register bool mode64bit

(* scattered function unit execute *)
scattered typedef ast = const union
scattered function ast decode
 union ast member  bit (* AA *) * bit [ 23 ] (* LI *) * bit (* LK *)  Branch 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitzero  ] as instr)) =
  Branch  (  instr[30] (* AA *), instr[6..29] (* LI *), instr[31] (* LK *)  ) 


 union ast member  bit (* AA *) * bit [ 13 ] (* BD *) * bit [ 4 ] (* BI *) * bit [ 4 ] (* BO *) * bit (* LK *)  BranchConditional 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitzero, 5 = bitzero  ] as instr)) =
  BranchConditional  (  instr[30] (* AA *), instr[16..29] (* BD *), instr[11..15] (* BI *), instr[6..10] (* BO *), instr[31] (* LK *)  ) 


 union ast member  bit [ 1 ] (* BH *) * bit [ 4 ] (* BI *) * bit [ 4 ] (* BO *) * bit (* LK *)  BranchConditionaltoLinkRegister 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  BranchConditionaltoLinkRegister  (  instr[19..20] (* BH *), instr[11..15] (* BI *), instr[6..10] (* BO *), instr[31] (* LK *)  ) 


 union ast member  bit [ 1 ] (* BH *) * bit [ 4 ] (* BI *) * bit [ 4 ] (* BO *) * bit (* LK *)  BranchConditionaltoCountRegister 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  BranchConditionaltoCountRegister  (  instr[19..20] (* BH *), instr[11..15] (* BI *), instr[6..10] (* BO *), instr[31] (* LK *)  ) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterAND 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterAND  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterNAND 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterNAND  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterOR 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitone, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterOR  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterXOR 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterXOR  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterNOR 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterNOR  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterEquivalent 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterEquivalent  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterANDwithComplement 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterANDwithComplement  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterORwithComplement 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterORwithComplement  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 


 union ast member  bit [ 2 ] (* BF *) * bit [ 2 ] (* BFA *)  MoveConditionRegisterField 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  MoveConditionRegisterField  (  instr[6..8] (* BF *), instr[11..13] (* BFA *)  ) 


 union ast member  bit [ 6 ] (* LEV *)  SystemCall 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitzero, 5 = bitone, 30 = bitone  ] as instr)) =
  SystemCall  (  instr[20..26] (* LEV *)  ) 


 union ast member  bit [ 6 ] (* LEV *)  SystemCallVectored 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitzero, 5 = bitone, 30 = bitzero, 31 = bitone  ] as instr)) =
  SystemCallVectored  (  instr[20..26] (* LEV *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadByteandZero 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitzero  ] as instr)) =
  LoadByteandZero  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadByteandZeroIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitone, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  LoadByteandZeroIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadByteandZerowithUpdate 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone  ] as instr)) =
  LoadByteandZerowithUpdate  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadByteandZerowithUpdateIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitone, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  LoadByteandZerowithUpdateIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadHalfwordandZero 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitone, 3 = bitzero, 4 = bitzero, 5 = bitzero  ] as instr)) =
  LoadHalfwordandZero  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadHalfwordandZeroIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  LoadHalfwordandZeroIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadHalfwordandZerowithUpdate 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitone, 3 = bitzero, 4 = bitzero, 5 = bitone  ] as instr)) =
  LoadHalfwordandZerowithUpdate  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadHalfwordandZerowithUpdateIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  LoadHalfwordandZerowithUpdateIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadHalfwordAlgebraic 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitone, 3 = bitzero, 4 = bitone, 5 = bitzero  ] as instr)) =
  LoadHalfwordAlgebraic  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadHalfwordAlgebraicIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitone, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  LoadHalfwordAlgebraicIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadHalfwordAlgebraicwithUpdate 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitone, 3 = bitzero, 4 = bitone, 5 = bitone  ] as instr)) =
  LoadHalfwordAlgebraicwithUpdate  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadHalfwordAlgebraicwithUpdateIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitone, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  LoadHalfwordAlgebraicwithUpdateIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadWordandZero 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitzero, 4 = bitzero, 5 = bitzero  ] as instr)) =
  LoadWordandZero  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadWordandZeroIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  LoadWordandZeroIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadWordandZerowithUpdate 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitzero, 4 = bitzero, 5 = bitone  ] as instr)) =
  LoadWordandZerowithUpdate  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadWordandZerowithUpdateIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  LoadWordandZerowithUpdateIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 13 ] (* DS *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadWordAlgebraic 

 function clause decode (([  0 = bitone, 1 = bitone, 2 = bitone, 3 = bitzero, 4 = bitone, 5 = bitzero, 30 = bitone, 31 = bitzero  ] as instr)) =
  LoadWordAlgebraic  (  instr[16..29] (* DS *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadWordAlgebraicIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitone, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  LoadWordAlgebraicIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadWordAlgebraicwithUpdateIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitone, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  LoadWordAlgebraicwithUpdateIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 13 ] (* DS *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadDoubleword 

 function clause decode (([  0 = bitone, 1 = bitone, 2 = bitone, 3 = bitzero, 4 = bitone, 5 = bitzero, 30 = bitzero, 31 = bitzero  ] as instr)) =
  LoadDoubleword  (  instr[16..29] (* DS *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadDoublewordIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  LoadDoublewordIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 13 ] (* DS *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadDoublewordwithUpdate 

 function clause decode (([  0 = bitone, 1 = bitone, 2 = bitone, 3 = bitzero, 4 = bitone, 5 = bitzero, 30 = bitzero, 31 = bitone  ] as instr)) =
  LoadDoublewordwithUpdate  (  instr[16..29] (* DS *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadDoublewordwithUpdateIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  LoadDoublewordwithUpdateIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreByte 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitone, 4 = bitone, 5 = bitzero  ] as instr)) =
  StoreByte  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  StoreByteIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  StoreByteIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreBytewithUpdate 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitone, 4 = bitone, 5 = bitone  ] as instr)) =
  StoreBytewithUpdate  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  StoreBytewithUpdateIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  StoreBytewithUpdateIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreHalfword 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitone, 3 = bitone, 4 = bitzero, 5 = bitzero  ] as instr)) =
  StoreHalfword  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  StoreHalfwordIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  StoreHalfwordIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreHalfwordwithUpdate 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitone, 3 = bitone, 4 = bitzero, 5 = bitone  ] as instr)) =
  StoreHalfwordwithUpdate  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  StoreHalfwordwithUpdateIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  StoreHalfwordwithUpdateIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreWord 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitone, 4 = bitzero, 5 = bitzero  ] as instr)) =
  StoreWord  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  StoreWordIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  StoreWordIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreWordwithUpdate 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitone, 4 = bitzero, 5 = bitone  ] as instr)) =
  StoreWordwithUpdate  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  StoreWordwithUpdateIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  StoreWordwithUpdateIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 13 ] (* DS *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreDoubleword 

 function clause decode (([  0 = bitone, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 30 = bitzero, 31 = bitzero  ] as instr)) =
  StoreDoubleword  (  instr[16..29] (* DS *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  StoreDoublewordIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  StoreDoublewordIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 13 ] (* DS *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreDoublewordwithUpdate 

 function clause decode (([  0 = bitone, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 30 = bitzero, 31 = bitone  ] as instr)) =
  StoreDoublewordwithUpdate  (  instr[16..29] (* DS *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  StoreDoublewordwithUpdateIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  StoreDoublewordwithUpdateIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 11 ] (* DQ *) * bit [ 3 ] (* PT *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RTp *)  LoadQuadword 

 function clause decode (([  0 = bitone, 1 = bitone, 2 = bitone, 3 = bitzero, 4 = bitzero, 5 = bitzero  ] as instr)) =
  LoadQuadword  (  instr[16..27] (* DQ *), instr[28..31] (* PT *), instr[11..15] (* RA *), instr[6..10] (* RTp *)  ) 


 union ast member  bit [ 13 ] (* DS *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RSp *)  StoreQuadword 

 function clause decode (([  0 = bitone, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 30 = bitone, 31 = bitzero  ] as instr)) =
  StoreQuadword  (  instr[16..29] (* DS *), instr[11..15] (* RA *), instr[6..10] (* RSp *)  ) 


 union ast member  bit [ 11 ] (* DQ *) * bit [ 1 ] (* EPT *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadTaggedPointer 

 function clause decode (([  0 = bitone, 1 = bitone, 2 = bitone, 3 = bitzero, 4 = bitzero, 5 = bitone, 30 = bitzero, 31 = bitone  ] as instr)) =
  LoadTaggedPointer  (  instr[16..27] (* DQ *), instr[28..29] (* EPT *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadHalfwordByteReverseIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitzero  ] as instr)) =
  LoadHalfwordByteReverseIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  StoreHalfwordByteReverseIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitzero  ] as instr)) =
  StoreHalfwordByteReverseIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadWordByteReverseIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitzero  ] as instr)) =
  LoadWordByteReverseIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  StoreWordByteReverseIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitone, 30 = bitzero  ] as instr)) =
  StoreWordByteReverseIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadDoublewordByteReverseIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  LoadDoublewordByteReverseIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  StoreDoublewordByteReverseIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  StoreDoublewordByteReverseIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadMultipleWord 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero  ] as instr)) =
  LoadMultipleWord  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 13 ] (* DS *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadMultipleDoubleword 

 function clause decode (([  0 = bitone, 1 = bitone, 2 = bitone, 3 = bitzero, 4 = bitone, 5 = bitzero, 30 = bitone, 31 = bitone  ] as instr)) =
  LoadMultipleDoubleword  (  instr[16..29] (* DS *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreMultipleWord 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone  ] as instr)) =
  StoreMultipleWord  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 13 ] (* DS *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreMultipleDoubleword 

 function clause decode (([  0 = bitone, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 30 = bitone, 31 = bitone  ] as instr)) =
  StoreMultipleDoubleword  (  instr[16..29] (* DS *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* NB *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadStringWordImmediate 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitone, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  LoadStringWordImmediate  (  instr[16..20] (* NB *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadStringWordIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  LoadStringWordIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* NB *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadStringDoublewordImmediate 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitone, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  LoadStringDoublewordImmediate  (  instr[16..20] (* NB *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  LoadStringDoublewordIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  LoadStringDoublewordIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* NB *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreStringWordImmediate 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  StoreStringWordImmediate  (  instr[16..20] (* NB *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  StoreStringWordIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  StoreStringWordIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* NB *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreStringDoublewordImmediate 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  StoreStringDoublewordImmediate  (  instr[16..20] (* NB *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  StoreStringDoublewordIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  StoreStringDoublewordIndexed  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *) * bit [ 15 ] (* SI *)  AddImmediate 

 function clause decode (([  0 = bitzero, 1 = bitzero, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero  ] as instr)) =
  AddImmediate  (  instr[11..15] (* RA *), instr[6..10] (* RT *), instr[16..31] (* SI *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *) * bit [ 15 ] (* SI *)  AddImmediateShifted 

 function clause decode (([  0 = bitzero, 1 = bitzero, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone  ] as instr)) =
  AddImmediateShifted  (  instr[11..15] (* RA *), instr[6..10] (* RT *), instr[16..31] (* SI *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  Add 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  Add  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  SubtractFrom 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  SubtractFrom  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *) * bit [ 15 ] (* SI *)  AddImmediateCarrying 

 function clause decode (([  0 = bitzero, 1 = bitzero, 2 = bitone, 3 = bitone, 4 = bitzero, 5 = bitzero  ] as instr)) =
  AddImmediateCarrying  (  instr[11..15] (* RA *), instr[6..10] (* RT *), instr[16..31] (* SI *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *) * bit [ 15 ] (* SI *)  AddImmediateCarryingandRecord 

 function clause decode (([  0 = bitzero, 1 = bitzero, 2 = bitone, 3 = bitone, 4 = bitzero, 5 = bitone  ] as instr)) =
  AddImmediateCarryingandRecord  (  instr[11..15] (* RA *), instr[6..10] (* RT *), instr[16..31] (* SI *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *) * bit [ 15 ] (* SI *)  SubtractFromImmediateCarrying 

 function clause decode (([  0 = bitzero, 1 = bitzero, 2 = bitone, 3 = bitzero, 4 = bitzero, 5 = bitzero  ] as instr)) =
  SubtractFromImmediateCarrying  (  instr[11..15] (* RA *), instr[6..10] (* RT *), instr[16..31] (* SI *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  AddCarrying 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  AddCarrying  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  SubtractFromCarrying 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  SubtractFromCarrying  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  AddExtended 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  AddExtended  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  SubtractFromExtended 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  SubtractFromExtended  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *) * bit (* Rc *)  AddtoMinusOneExtended 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  AddtoMinusOneExtended  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *) * bit (* Rc *)  SubtractFromMinusOneExtended 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  SubtractFromMinusOneExtended  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *) * bit (* Rc *)  AddtoZeroExtended 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  AddtoZeroExtended  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *) * bit (* Rc *)  SubtractFromZeroExtended 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  SubtractFromZeroExtended  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *) * bit (* Rc *)  Negate 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitone, 25 = bitone, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  Negate  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *) * bit [ 15 ] (* SI *)  MultiplyLowImmediate 

 function clause decode (([  0 = bitzero, 1 = bitzero, 2 = bitzero, 3 = bitone, 4 = bitone, 5 = bitone  ] as instr)) =
  MultiplyLowImmediate  (  instr[11..15] (* RA *), instr[6..10] (* RT *), instr[16..31] (* SI *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  MultiplyLowWord 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  MultiplyLowWord  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  MultiplyHighWord 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitone, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  MultiplyHighWord  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  MultiplyHighWordUnsigned 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  MultiplyHighWordUnsigned  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  DivideWord 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitone, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  DivideWord  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  DivideWordUnsigned 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitone, 23 = bitone, 24 = bitone, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  DivideWordUnsigned  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  DivideWordExtended 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  DivideWordExtended  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  DivideWordExtendedUnsigned 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  DivideWordExtendedUnsigned  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  MultiplyLowDoubleword 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  MultiplyLowDoubleword  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  MultiplyHighDoubleword 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitone, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  MultiplyHighDoubleword  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  MultiplyHighDoublewordUnsigned 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  MultiplyHighDoublewordUnsigned  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  DivideDoubleword 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitone, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  DivideDoubleword  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  DivideDoublewordUnsigned 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitone, 23 = bitone, 24 = bitone, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  DivideDoublewordUnsigned  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  DivideDoublewordExtended 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  DivideDoublewordExtended  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit (* OE *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *) * bit (* Rc *)  DivideDoublewordExtendedUnsigned 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  DivideDoublewordExtendedUnsigned  (  instr[21] (* OE *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 2 ] (* BF *) * bit (* L *) * bit [ 4 ] (* RA *) * bit [ 15 ] (* SI *)  CompareImmediate 

 function clause decode (([  0 = bitzero, 1 = bitzero, 2 = bitone, 3 = bitzero, 4 = bitone, 5 = bitone  ] as instr)) =
  CompareImmediate  (  instr[6..8] (* BF *), instr[10] (* L *), instr[11..15] (* RA *), instr[16..31] (* SI *)  ) 


 union ast member  bit [ 2 ] (* BF *) * bit (* L *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *)  Compare 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  Compare  (  instr[6..8] (* BF *), instr[10] (* L *), instr[11..15] (* RA *), instr[16..20] (* RB *)  ) 


 union ast member  bit [ 2 ] (* BF *) * bit (* L *) * bit [ 4 ] (* RA *) * bit [ 15 ] (* UI *)  CompareLogicalImmediate 

 function clause decode (([  0 = bitzero, 1 = bitzero, 2 = bitone, 3 = bitzero, 4 = bitone, 5 = bitzero  ] as instr)) =
  CompareLogicalImmediate  (  instr[6..8] (* BF *), instr[10] (* L *), instr[11..15] (* RA *), instr[16..31] (* UI *)  ) 


 union ast member  bit [ 2 ] (* BF *) * bit (* L *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *)  CompareLogical 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  CompareLogical  (  instr[6..8] (* BF *), instr[10] (* L *), instr[11..15] (* RA *), instr[16..20] (* RB *)  ) 


 union ast member  bit [ 2 ] (* BF *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *)  CompareLogicalAddresses 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 10 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitone, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  CompareLogicalAddresses  (  instr[6..8] (* BF *), instr[11..15] (* RA *), instr[16..20] (* RB *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 15 ] (* SI *) * bit [ 4 ] (* TO *)  TrapWordImmediate 

 function clause decode (([  0 = bitzero, 1 = bitzero, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone  ] as instr)) =
  TrapWordImmediate  (  instr[11..15] (* RA *), instr[16..31] (* SI *), instr[6..10] (* TO *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* TO *)  TrapWord 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  TrapWord  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* TO *)  ) 


 union ast member  bit [ 4 ] (* TO *) * bit [ 9 ] (* UI *) * bit [ 3 ] (* XBI *)  TraponXER 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 25 = bitone, 26 = bitzero, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  TraponXER  (  instr[6..10] (* TO *), instr[11..20] (* UI *), instr[21..24] (* XBI *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 15 ] (* SI *) * bit [ 4 ] (* TO *)  TrapDoublewordImmediate 

 function clause decode (([  0 = bitzero, 1 = bitzero, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitzero  ] as instr)) =
  TrapDoublewordImmediate  (  instr[11..15] (* RA *), instr[16..31] (* SI *), instr[6..10] (* TO *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* TO *)  TrapDoubleword 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitone, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  TrapDoubleword  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* TO *)  ) 


 union ast member  bit [ 4 ] (* IB *) * bit [ 4 ] (* IS *) * bit [ 4 ] (* RA *) * bit (* Rc *) * bit [ 3 ] (* XBI *)  SelectImmediateImmediate 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  SelectImmediateImmediate  (  instr[16..20] (* IB *), instr[6..10] (* IS *), instr[11..15] (* RA *), instr[31] (* Rc *), instr[21..24] (* XBI *)  ) 


 union ast member  bit [ 4 ] (* IS *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit (* Rc *) * bit [ 3 ] (* XBI *)  SelectImmediateRegister 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  SelectImmediateRegister  (  instr[6..10] (* IS *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[31] (* Rc *), instr[21..24] (* XBI *)  ) 


 union ast member  bit [ 4 ] (* IB *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *) * bit [ 3 ] (* XBI *)  SelectRegisterImmediate 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 27 = bitone, 28 = bitone, 29 = bitone, 30 = bitzero  ] as instr)) =
  SelectRegisterImmediate  (  instr[16..20] (* IB *), instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *), instr[21..24] (* XBI *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *) * bit [ 3 ] (* XBI *)  SelectRegisterRegister 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 27 = bitone, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  SelectRegisterRegister  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *), instr[21..24] (* XBI *)  ) 


 union ast member  bit [ 4 ] (* BC *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  IntegerSelect 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 26 = bitzero, 27 = bitone, 28 = bitone, 29 = bitone, 30 = bitone  ] as instr)) =
  IntegerSelect  (  instr[21..25] (* BC *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit [ 15 ] (* UI *)  ANDImmediate 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitzero, 5 = bitzero  ] as instr)) =
  ANDImmediate  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[16..31] (* UI *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit [ 15 ] (* UI *)  ANDImmediateShifted 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitzero, 5 = bitone  ] as instr)) =
  ANDImmediateShifted  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[16..31] (* UI *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit [ 15 ] (* UI *)  ORImmediate 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitzero, 4 = bitzero, 5 = bitzero  ] as instr)) =
  ORImmediate  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[16..31] (* UI *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit [ 15 ] (* UI *)  ORImmediateShifted 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitzero, 4 = bitzero, 5 = bitone  ] as instr)) =
  ORImmediateShifted  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[16..31] (* UI *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit [ 15 ] (* UI *)  XORImmediate 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitzero, 4 = bitone, 5 = bitzero  ] as instr)) =
  XORImmediate  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[16..31] (* UI *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit [ 15 ] (* UI *)  XORImmediateShifted 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitzero, 4 = bitone, 5 = bitone  ] as instr)) =
  XORImmediateShifted  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[16..31] (* UI *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  AND 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  AND  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  XOR 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  XOR  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  NAND 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitone, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  NAND  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  OR 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  OR  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  NOR 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitone, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  NOR  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  Equivalent 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  Equivalent  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  ANDwithComplement 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  ANDwithComplement  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  ORwithComplement 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  ORwithComplement  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *)  ExtendSignByte 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  ExtendSignByte  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *)  ExtendSignHalfword 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  ExtendSignHalfword  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *)  CountLeadingZerosWord 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  CountLeadingZerosWord  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  CompareBytes 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  CompareBytes  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  PopulationCountBytes 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitone, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  PopulationCountBytes  (  instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  PopulationCountWords 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitone, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  PopulationCountWords  (  instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  ParityDoubleword 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  ParityDoubleword  (  instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  ParityWord 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  ParityWord  (  instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *)  ExtendSignWord 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitone, 23 = bitone, 24 = bitone, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  ExtendSignWord  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *)  CountLeadingZerosDoubleword 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  CountLeadingZerosDoubleword  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  PopulationCountDoubleword 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  PopulationCountDoubleword  (  instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *)  BitPermuteDoubleword 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  BitPermuteDoubleword  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* MB *) * bit [ 4 ] (* ME *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *) * bit [ 4 ] (* SH *)  RotateLeftWordImmediatethenANDwithMask 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitone, 4 = bitzero, 5 = bitone  ] as instr)) =
  RotateLeftWordImmediatethenANDwithMask  (  instr[21..25] (* MB *), instr[26..30] (* ME *), instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *), instr[16..20] (* SH *)  ) 


 union ast member  bit [ 4 ] (* MB *) * bit [ 4 ] (* ME *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  RotateLeftWordthenANDwithMask 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitone, 4 = bitone, 5 = bitone  ] as instr)) =
  RotateLeftWordthenANDwithMask  (  instr[21..25] (* MB *), instr[26..30] (* ME *), instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* MB *) * bit [ 4 ] (* ME *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *) * bit [ 4 ] (* SH *)  RotateLeftWordImmediatethenMaskInsert 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitone, 4 = bitzero, 5 = bitzero  ] as instr)) =
  RotateLeftWordImmediatethenMaskInsert  (  instr[21..25] (* MB *), instr[26..30] (* ME *), instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *), instr[16..20] (* SH *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *) * bit [ 5 ] (* mb *) * bit [ 5 ] (* sh *)  RotateLeftDoublewordImmediatethenClearLeft 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero  ] as instr)) =
  RotateLeftDoublewordImmediatethenClearLeft  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *), instr[21..26] (* mb *), instr[16..20] : instr[30] (* sh *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *) * bit [ 5 ] (* me *) * bit [ 5 ] (* sh *)  RotateLeftDoublewordImmediatethenClearRight 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitone  ] as instr)) =
  RotateLeftDoublewordImmediatethenClearRight  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *), instr[21..26] (* me *), instr[16..20] : instr[30] (* sh *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *) * bit [ 5 ] (* mb *) * bit [ 5 ] (* sh *)  RotateLeftDoublewordImmediatethenClear 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 27 = bitzero, 28 = bitone, 29 = bitzero  ] as instr)) =
  RotateLeftDoublewordImmediatethenClear  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *), instr[21..26] (* mb *), instr[16..20] : instr[30] (* sh *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *) * bit [ 5 ] (* mb *)  RotateLeftDoublewordthenClearLeft 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  RotateLeftDoublewordthenClearLeft  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *), instr[21..26] (* mb *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *) * bit [ 5 ] (* me *)  RotateLeftDoublewordthenClearRight 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  RotateLeftDoublewordthenClearRight  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *), instr[21..26] (* me *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *) * bit [ 5 ] (* mb *) * bit [ 5 ] (* sh *)  RotateLeftDoublewordImmediatethenMaskInsert 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero, 27 = bitzero, 28 = bitone, 29 = bitone  ] as instr)) =
  RotateLeftDoublewordImmediatethenMaskInsert  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *), instr[21..26] (* mb *), instr[16..20] : instr[30] (* sh *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  ShiftLeftWord 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  ShiftLeftWord  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  ShiftRightWord 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  ShiftRightWord  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *) * bit [ 4 ] (* SH *)  ShiftRightAlgebraicWordImmediate 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  ShiftRightAlgebraicWordImmediate  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *), instr[16..20] (* SH *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  ShiftRightAlgebraicWord 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  ShiftRightAlgebraicWord  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  ShiftLeftDoubleword 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  ShiftLeftDoubleword  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  ShiftRightDoubleword 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  ShiftRightDoubleword  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *) * bit (* Rc *) * bit [ 5 ] (* sh *)  ShiftRightAlgebraicDoublewordImmediate 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone  ] as instr)) =
  ShiftRightAlgebraicDoublewordImmediate  (  instr[11..15] (* RA *), instr[6..10] (* RS *), instr[31] (* Rc *), instr[16..20] : instr[30] (* sh *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  ShiftRightAlgebraicDoubleword 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  ShiftRightAlgebraicDoubleword  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  ConvertDecletsToBinaryCodedDecimal 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  ConvertDecletsToBinaryCodedDecimal  (  instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  ConvertBinaryCodedDecimalToDeclets 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  ConvertBinaryCodedDecimalToDeclets  (  instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RT *)  AddandGenerateSixes 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitone, 25 = bitzero, 26 = bitzero, 27 = bitone, 28 = bitzero, 29 = bitone, 30 = bitzero  ] as instr)) =
  AddandGenerateSixes  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 4 ] (* RA *)  DecimalSixes 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitone  ] as instr)) =
  DecimalSixes  (  instr[11..15] (* RA *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  DecimalTestandClearSign 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitone, 25 = bitzero, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitone, 31 = bitone  ] as instr)) =
  DecimalTestandClearSign  (  instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RS *) * bit [ 9 ] (* spr *)  MoveToSpecialPurposeRegister 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitone, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  MoveToSpecialPurposeRegister  (  instr[6..10] (* RS *), instr[11..20] (* spr *)  ) 


 union ast member  bit [ 4 ] (* RT *) * bit [ 9 ] (* spr *)  MoveFromSpecialPurposeRegister 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitone, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  MoveFromSpecialPurposeRegister  (  instr[6..10] (* RT *), instr[11..20] (* spr *)  ) 


 union ast member  SetXERTAG 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 15 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitone, 27 = bitzero, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  SetXERTAG 


 union ast member  bit [ 7 ] (* FXM *) * bit [ 4 ] (* RS *)  MoveToConditionRegisterFields 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 11 = bitzero, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  MoveToConditionRegisterFields  (  instr[12..19] (* FXM *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RT *)  MoveFromConditionRegister 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 11 = bitzero, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  MoveFromConditionRegister  (  instr[6..10] (* RT *)  ) 


 union ast member  bit [ 2 ] (* BF *)  MovetoConditionRegisterfromXERTGCC 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  MovetoConditionRegisterfromXERTGCC  (  instr[6..8] (* BF *)  ) 


 union ast member  bit [ 7 ] (* FXM *) * bit [ 4 ] (* RS *)  MoveToOneConditionRegisterField 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 11 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  MoveToOneConditionRegisterField  (  instr[12..19] (* FXM *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 7 ] (* FXM *) * bit [ 4 ] (* RT *)  MoveFromOneConditionRegisterField 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 11 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  MoveFromOneConditionRegisterField  (  instr[12..19] (* FXM *), instr[6..10] (* RT *)  ) 


 union ast member  bit [ 2 ] (* BF *)  MovetoConditionRegisterfromXER 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  MovetoConditionRegisterfromXER  (  instr[6..8] (* BF *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  MoveToDeviceControlRegisterUsermodeIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  MoveToDeviceControlRegisterUsermodeIndexed  (  instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 


 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  MoveFromDeviceControlRegisterUsermodeIndexed 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitone, 30 = bitone  ] as instr)) =
  MoveFromDeviceControlRegisterUsermodeIndexed  (  instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 


end decode
(* end execute *)
end ast

register ast instr (* monitor decoded instructions *)

function rec unit main () = {
  NIA := CIA + 4;
  instr := decode(MEM(CIA, 4));
  (* execute(instr); *)
  CIA := NIA;
  main ()
}
