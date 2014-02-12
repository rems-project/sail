val extern ( nat * nat ) -> nat effect pure (deinfix + ) = "add"
(* XXX type is wrong *)
val extern forall Type 'a . ( 'a * 'a ) -> 'a effect pure (deinfix : ) = "vec_concat"

val extern forall Type 'a . ( 'a * 'a ) -> bit effect pure (deinfix != ) = "neq"

val extern forall Type 'a . ( 'a * 'a ) -> bool effect pure (deinfix != ) = "neq"

val extern bit -> bit effect pure (deinfix ~ ) = "bitwise-not"
val extern ( bit * bit ) -> bit effect pure (deinfix ^ ) = "bitwise-xor"
val extern ( bit * bit ) -> bit effect pure (deinfix & ) = "bitwise-and"

val extern bit -> bool effect pure is_one = "is_one"

(* XXX sign extension *)
function forall Type 'a . 'a exts ( x ) = x

register (bit[32]) NIA (* next instruction address *)
register (bit[32]) CIA (* current instruction address *)

(* XXX check me *)
register (bit[32]) CR
register (bit[32]) CTR
register (bit[32]) LR

register bool mode64bit

scattered function unit execute
scattered typedef ast = const union
scattered function ast decode
 union ast member  bit (* AA *) * bit [ 23 ] (* LI *) * bit (* LK *)  Branch 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitzero  ] as instr)) =
  Branch  (  instr[30] (* AA *), instr[6..29] (* LI *), instr[31] (* LK *)  ) 

 function clause execute (  Branch  (  AA, LI, LK  )  ) =
  {
    if  AA  then  NIA  :=  (  exts  (  (  LI  :  0b00  )  ))  else  NIA  :=  (  CIA  +  (  exts  (  (  LI  :  0b00  )  ))  )  ;
    if  LK  then  LR  :=  (  CIA  +  4  )  ;
  } 


 union ast member  bit (* AA *) * bit [ 13 ] (* BD *) * bit [ 4 ] (* BI *) * bit [ 4 ] (* BO *) * bit (* LK *)  BranchConditional 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitzero, 5 = bitzero  ] as instr)) =
  BranchConditional  (  instr[30] (* AA *), instr[16..29] (* BD *), instr[11..15] (* BI *), instr[6..10] (* BO *), instr[31] (* LK *)  ) 

 function clause execute (  BranchConditional  (  AA, BD, BI, BO, LK  )  ) =
  {
    if  mode64bit  then  M  :=  0  else  M  :=  32  ;
    if  (  ~  (  ((  BO  )[  2  ])  ))  then  CTR  :=  (  CTR  -  1  )  ;
    ctr_ok  :=  (  ((  BO  )[  2  ])  |  (  (  ((  CTR  )[  M  ..  63  ])  !=  0  )  ^  ((  BO  )[  3  ])  )  )  ;
    cond_ok  :=  (  ((  BO  )[  0  ])  |  (  ((  CR  )[  (  BI  +  32  )  ])  ^  (  ~  (  ((  BO  )[  1  ])  ))  )  )  ;
    if  (  ctr_ok  &  cond_ok  )  then  {
      if  AA  then  NIA  :=  (  exts  (  (  BD  :  0b00  )  ))  else  NIA  :=  (  CIA  +  (  exts  (  (  BD  :  0b00  )  ))  )  ;
    }  ;
    if  LK  then  LR  :=  (  CIA  +  4  )  ;
  } 


 union ast member  bit [ 1 ] (* BH *) * bit [ 4 ] (* BI *) * bit [ 4 ] (* BO *) * bit (* LK *)  BranchConditionaltoLinkRegister 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  BranchConditionaltoLinkRegister  (  instr[19..20] (* BH *), instr[11..15] (* BI *), instr[6..10] (* BO *), instr[31] (* LK *)  ) 

 function clause execute (  BranchConditionaltoLinkRegister  (  BH, BI, BO, LK  )  ) =
  {
    if  mode64bit  then  M  :=  0  else  M  :=  32  ;
    if  (  ~  (  ((  BO  )[  2  ])  ))  then  CTR  :=  (  CTR  -  1  )  ;
    ctr_ok  :=  (  ((  BO  )[  2  ])  |  (  (  ((  CTR  )[  M  ..  63  ])  !=  0  )  ^  ((  BO  )[  3  ])  )  )  ;
    cond_ok  :=  (  ((  BO  )[  0  ])  |  (  ((  CR  )[  (  BI  +  32  )  ])  ^  (  ~  (  ((  BO  )[  1  ])  ))  )  )  ;
    if  (  ctr_ok  &  cond_ok  )  then  NIA  :=  (  ((  LR  )[  0  ..  61  ])  :  0b00  )  ;
    if  LK  then  LR  :=  (  CIA  +  4  )  ;
  } 


 union ast member  bit [ 1 ] (* BH *) * bit [ 4 ] (* BI *) * bit [ 4 ] (* BO *) * bit (* LK *)  BranchConditionaltoCountRegister 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitone, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  BranchConditionaltoCountRegister  (  instr[19..20] (* BH *), instr[11..15] (* BI *), instr[6..10] (* BO *), instr[31] (* LK *)  ) 

 function clause execute (  BranchConditionaltoCountRegister  (  BH, BI, BO, LK  )  ) =
  {
    cond_ok  :=  (  ((  BO  )[  0  ])  |  (  ((  CR  )[  (  BI  +  32  )  ])  ^  (  ~  (  ((  BO  )[  1  ])  ))  )  )  ;
    if  cond_ok  then  NIA  :=  (  ((  CTR  )[  0  ..  61  ])  :  0b00  )  ;
    if  LK  then  LR  :=  (  CIA  +  4  )  ;
  } 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterAND 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterAND  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 

 function clause execute (  ConditionRegisterAND  (  BA, BB, BT  )  ) =
  (  CR  )[  (  BT  +  32  )  ] :=   (  ((  CR  )[  (  BA  +  32  )  ])  &  ((  CR  )[  (  BB  +  32  )  ])  ) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterNAND 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitone, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterNAND  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 

 function clause execute (  ConditionRegisterNAND  (  BA, BB, BT  )  ) =
  (  CR  )[  (  BT  +  32  )  ] :=   (  ~  (  (  ((  CR  )[  (  BA  +  32  )  ])  &  ((  CR  )[  (  BB  +  32  )  ])  )  )) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterOR 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitone, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterOR  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 

 function clause execute (  ConditionRegisterOR  (  BA, BB, BT  )  ) =
  (  CR  )[  (  BT  +  32  )  ] :=   (  ((  CR  )[  (  BA  +  32  )  ])  |  ((  CR  )[  (  BB  +  32  )  ])  ) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterXOR 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitone, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterXOR  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 

 function clause execute (  ConditionRegisterXOR  (  BA, BB, BT  )  ) =
  (  CR  )[  (  BT  +  32  )  ] :=   (  ((  CR  )[  (  BA  +  32  )  ])  ^  ((  CR  )[  (  BB  +  32  )  ])  ) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterNOR 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterNOR  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 

 function clause execute (  ConditionRegisterNOR  (  BA, BB, BT  )  ) =
  (  CR  )[  (  BT  +  32  )  ] :=   (  ~  (  (  ((  CR  )[  (  BA  +  32  )  ])  |  ((  CR  )[  (  BB  +  32  )  ])  )  )) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterEquivalent 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitzero, 24 = bitzero, 25 = bitone, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterEquivalent  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 

 function clause execute (  ConditionRegisterEquivalent  (  BA, BB, BT  )  ) =
  (  CR  )[  (  BT  +  32  )  ] :=   (  ((  CR  )[  (  BA  +  32  )  ])  ^  (  ~  (  ((  CR  )[  (  BB  +  32  )  ])  ))  ) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterANDwithComplement 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitone, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterANDwithComplement  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 

 function clause execute (  ConditionRegisterANDwithComplement  (  BA, BB, BT  )  ) =
  (  CR  )[  (  BT  +  32  )  ] :=   (  ((  CR  )[  (  BA  +  32  )  ])  &  (  ~  (  ((  CR  )[  (  BB  +  32  )  ])  ))  ) 


 union ast member  bit [ 4 ] (* BA *) * bit [ 4 ] (* BB *) * bit [ 4 ] (* BT *)  ConditionRegisterORwithComplement 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitone  ] as instr)) =
  ConditionRegisterORwithComplement  (  instr[11..15] (* BA *), instr[16..20] (* BB *), instr[6..10] (* BT *)  ) 

 function clause execute (  ConditionRegisterORwithComplement  (  BA, BB, BT  )  ) =
  (  CR  )[  (  BT  +  32  )  ] :=   (  ((  CR  )[  (  BA  +  32  )  ])  |  (  ~  (  ((  CR  )[  (  BB  +  32  )  ])  ))  ) 


 union ast member  bit [ 2 ] (* BF *) * bit [ 2 ] (* BFA *)  MoveConditionRegisterField 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitzero, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  MoveConditionRegisterField  (  instr[6..8] (* BF *), instr[11..13] (* BFA *)  ) 

 function clause execute (  MoveConditionRegisterField  (  BF, BFA  )  ) =
  (  CR  )[  (  (  4  *  BF  )  +  32  )  ..  (  (  4  *  BF  )  +  35  )  ] :=   ((  CR  )[  (  (  4  *  BFA  )  +  32  )  ..  (  (  4  *  BFA  )  +  35  )  ]) 


 union ast member  bit [ 6 ] (* LEV *)  SystemCall 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitzero, 5 = bitone, 30 = bitone  ] as instr)) =
  SystemCall  (  instr[20..26] (* LEV *)  ) 

 function clause execute (  SystemCall  (  LEV  )  ) =
      () 


 union ast member  bit [ 6 ] (* LEV *)  SystemCallVectored 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitzero, 5 = bitone, 30 = bitzero, 31 = bitone  ] as instr)) =
  SystemCallVectored  (  instr[20..26] (* LEV *)  ) 

 function clause execute (  SystemCallVectored  (  LEV  )  ) =
      () 


end decode
end execute
end ast

function unit main _ = {
  (* init *)
  CIA := 0b0;
  NIA := 0b0;

  (* should decode as Branch *)
  execute(decode(0b01001000000000000000000000000000));
  ()
}
