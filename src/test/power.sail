(* XXX types are wrong *)
val extern forall Type 'a, Type 'b, Type 'c . ( 'a * 'b ) -> 'c effect pure (deinfix + ) = "add"
val extern forall Type 'a . ( 'a * 'a ) -> 'a effect pure (deinfix mod ) = "mod"
val extern forall Type 'a, Type 'b, Type 'c .
  ( 'a * 'b ) -> 'c effect pure (deinfix : ) = "vec_concat"
val extern forall Type 'a . 'a -> nat effect pure to_num_inc = "to_num_inc"
val extern forall Type 'a . 'a -> nat effect pure to_num_dec = "to_num_dec"
val extern forall Type 'a . nat -> 'a effect pure to_vec_inc = "to_vec_inc"
val extern forall Type 'a . nat -> 'a effect pure to_vec_dec = "to_vec_dec"

val extern forall Type 'a . ( 'a * 'a ) -> bit effect pure (deinfix == ) = "eq"
val extern forall Type 'a . ( 'a * 'a ) -> bit effect pure (deinfix != ) = "neq"

val extern forall Type 'a . 'a -> 'a effect pure (deinfix ~ ) = "bitwise-not"
val extern forall Type 'a . ( 'a * 'a ) -> 'a effect pure (deinfix ^ ) = "bitwise-xor"
val extern forall Type 'a . ( 'a * 'a ) -> 'a effect pure (deinfix || ) = "bitwise-or"
val extern forall Type 'a . ( 'a * 'a ) -> 'a effect pure (deinfix & ) = "bitwise-and"

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

register (bit[64]) XER
let nat SO = 32
let nat OV = 33
let nat CA = 34

val extern ( nat * nat ) -> (bit[64]) effect { wmem , rmem } MEM

register bool mode64bit

scattered function unit execute
scattered typedef ast = const union
scattered function ast decode
 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *) * bit [ 15 ] (* SI *)  AddImmediate 

 function clause decode (([  0 = bitzero, 1 = bitzero, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero  ] as instr)) =
  AddImmediate  (  instr[11..15] (* RA *), instr[6..10] (* RT *), instr[16..31] (* SI *)  ) 

 function clause execute (  AddImmediate  (  RA, RT, SI  )  ) =
  {
    if  (  RA  ==  0  )  then  GPR[  RT  ]  :=  (  exts  (  SI  ))  else  GPR[  RT  ]  :=  (  (GPR[  RA  ])  +  (  exts  (  SI  ))  )  ;
  } 

 union ast member  bit [ 1 ] (* BH *) * bit [ 4 ] (* BI *) * bit [ 4 ] (* BO *) * bit (* LK *)  BranchConditionaltoLinkRegister 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  BranchConditionaltoLinkRegister  (  instr[19..20] (* BH *), instr[11..15] (* BI *), instr[6..10] (* BO *), instr[31] (* LK *)  ) 

 function clause execute (  BranchConditionaltoLinkRegister  (  BH, BI, BO, LK  )  ) =
  {
    if  mode64bit  then  M  :=  0  else  M  :=  32  ;
    if  (  ~  (  ((  BO  )[  2  ])  ))  then  CTR  :=  (  CTR  -  1  )  ;
    ctr_ok  :=  (  ((  BO  )[  2  ])  ||  (  (  ((  CTR  )[  M  ..  63  ])  !=  0  )  ^  ((  BO  )[  3  ])  )  )  ;
    cond_ok  :=  (  ((  BO  )[  0  ])  ||  (  ((  CR  )[  (  BI  +  32  )  ])  ^  (  ~  (  ((  BO  )[  1  ])  ))  )  )  ;
    if  (  ctr_ok  &  cond_ok  )  then  NIA  :=  (  ((  LR  )[  0  ..  61  ])  :  0b00  )  ;
    if  LK  then  LR  :=  (  CIA  +  4  )  ;
  } 


 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RT *)  LoadWordandZero 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitzero, 4 = bitzero, 5 = bitzero  ] as instr)) =
  LoadWordandZero  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 

 function clause execute (  LoadWordandZero  (  D, RA, RT  )  ) =
  {
    if  (  RA  ==  0  )  then  b  :=  0  else  b  :=  (GPR[  RA  ])  ;
    EA  :=  (  b  +  (  exts  (  D  ))  )  ;
    GPR[  RT  ]  :=  (  0b00000000000000000000000000000000  :  MEM(  EA  ,   4  )  )  ;
  } 

 union ast member  bit [ 4 ] (* RA *) * bit [ 4 ] (* RB *) * bit [ 4 ] (* RS *) * bit (* Rc *)  OR 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  OR  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 

 function clause execute (  OR  (  RA, RB, RS, Rc  )  ) =
  GPR[  RA  ]  :=  (  (GPR[  RS  ])  ||  (GPR[  RB  ])  ) 

 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreWord 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitone, 4 = bitzero, 5 = bitzero  ] as instr)) =
  StoreWord  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 

 function clause execute (  StoreWord  (  D, RA, RS  )  ) =
  {
    if  (  RA  ==  0  )  then  b  :=  0  else  b  :=  (GPR[  RA  ])  ;
    EA  :=  (  b  +  (  exts  (  D  ))  )  ;
    MEM(  EA  ,   4  )  :=  ((  (GPR[  RS  ])  )[  32  ..  63  ])  ;
  } 

 union ast member  bit [ 15 ] (* D *) * bit [ 4 ] (* RA *) * bit [ 4 ] (* RS *)  StoreWordwithUpdate 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitone, 4 = bitzero, 5 = bitone  ] as instr)) =
  StoreWordwithUpdate  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 

 function clause execute (  StoreWordwithUpdate  (  D, RA, RS  )  ) =
  {
    EA  :=  (  (GPR[  RA  ])  +  (  exts  (  D  ))  )  ;
    MEM(  EA  ,   4  )  :=  ((  (GPR[  RS  ])  )[  32  ..  63  ])  ;
    GPR[  RA  ]  :=  EA  ;
  } 


end decode
end execute
end ast

register ast instr (* monitor decoded instructions *)

function rec unit main () = {
  NIA := CIA + 4;
  instr := decode(MEM(CIA, 4));
  execute(instr);
  CIA := NIA;
  main ()
}
