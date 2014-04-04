(* XXX sign extension --- note that this produces a signed integer,
   the constraints on the range of the result is TODO *)
val extern forall Nat 'n. bit['n] -> nat effect pure exts
(* XXX binary coded decimal *)
function forall Type 'a . 'a dec_to_bcd ( x ) = x
function forall Type 'a . 'a bcd_to_dec ( x ) = x
(* XXX carry out *)
function bit carry_out ( x ) = bitzero
(* XXX length *)
function nat length ( x ) = 64

val forall Nat 'n, Nat 'm, 0 <= 'n, 'n <= 'm, 'm <= 63 .
  ([|'n|],[|'m|]) -> bit[64]
  effect pure
  MASK

function (bit[64]) MASK(start, stop) = {
  (bit[64]) mask := 0;
  if(start > stop) then {
    mask[start .. 63] := bitone ^^ (64 - start);
    mask[0 .. stop] := bitone ^^ (stop + 1);
  } else {
    mask[start .. stop ] := bitone ^^ (stop - start + 1);
  };
  mask;
} 

register (vector <0, 64, inc, bit>) GPR0
register (vector <0, 64, inc, bit>) GPR1
register (vector <0, 64, inc, bit>) GPR2
register (vector <0, 64, inc, bit>) GPR3
register (vector <0, 64, inc, bit>) GPR4
register (vector <0, 64, inc, bit>) GPR5
register (vector <0, 64, inc, bit>) GPR6
register (vector <0, 64, inc, bit>) GPR7
register (vector <0, 64, inc, bit>) GPR8
register (vector <0, 64, inc, bit>) GPR9
register (vector <0, 64, inc, bit>) GPR10
register (vector <0, 64, inc, bit>) GPR11
register (vector <0, 64, inc, bit>) GPR12
register (vector <0, 64, inc, bit>) GPR13
register (vector <0, 64, inc, bit>) GPR14
register (vector <0, 64, inc, bit>) GPR15
register (vector <0, 64, inc, bit>) GPR16
register (vector <0, 64, inc, bit>) GPR17
register (vector <0, 64, inc, bit>) GPR18
register (vector <0, 64, inc, bit>) GPR19
register (vector <0, 64, inc, bit>) GPR20
register (vector <0, 64, inc, bit>) GPR21
register (vector <0, 64, inc, bit>) GPR22
register (vector <0, 64, inc, bit>) GPR23
register (vector <0, 64, inc, bit>) GPR24
register (vector <0, 64, inc, bit>) GPR25
register (vector <0, 64, inc, bit>) GPR26
register (vector <0, 64, inc, bit>) GPR27
register (vector <0, 64, inc, bit>) GPR28
register (vector <0, 64, inc, bit>) GPR29
register (vector <0, 64, inc, bit>) GPR30
register (vector <0, 64, inc, bit>) GPR31

let (vector <0, 32, inc, (register<(vector<0, 64, inc, bit>)>) >) GPR =
  [ GPR0, GPR1, GPR2, GPR3, GPR4, GPR5, GPR6, GPR7, GPR8, GPR9, GPR10,
  GPR11, GPR12, GPR13, GPR14, GPR15, GPR16, GPR17, GPR18, GPR19, GPR20,
  GPR21, GPR22, GPR23, GPR24, GPR25, GPR26, GPR27, GPR28, GPR29, GPR30, GPR31
  ]

register (bit[64]) NIA (* next instruction address *)
register (bit[64]) CIA (* current instruction address *)

register (bit[32 : 63]) CR
register (bit[64]) CTR
register (bit[64]) LR

register (bit[64]) XER
let nat SO = 32
let nat OV = 33
let nat CA = 34

(* XXX bogus, length should be 1024 with many more values - cf. mfspr
  definition *)
let (vector <0, 10, inc, (register<(vector<0, 64, inc, bit>)>) >) SPR =
  [ undefined, XER, undefined, undefined, undefined, undefined, undefined, undefined, LR,
    CTR ]

(* XXX bogus, DCR might be numbered with 64-bit values! -
 and it's implementation-dependent; also, some DCR are only 32 bits
 instead of 64, and mtdcrux/mfdcrux do special tricks in that case, not
 shown in pseudo-code (?) *)
register (vector <0, 64, inc, bit>) DCR0
register (vector <0, 64, inc, bit>) DCR1
let (vector <0, 2, inc, (register<(vector<0, 64, inc, bit>)>) >) DCR =
  [ DCR0, DCR1 ]

val extern ( nat , nat ) -> (bit[64]) effect { wmem , rmem } MEM

(* XXX effect for trap? *)
val extern unit -> unit effect pure trap

(* XXX should be register<bool>, this is a workaround for limitations in coercions *)
let (bit) mode64bit = bitone

scattered function unit execute
scattered typedef ast = const union
scattered function ast decode

 union ast member  (  bit [ 2 ] (* BH *) , bit [ 5 ] (* BI *) , bit [ 5 ] (* BO *) , bit (* LK *)  )  BranchConditionaltoLinkRegister 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitzero, 3 = bitzero, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitzero, 23 = bitzero, 24 = bitzero, 25 = bitzero, 26 = bitone, 27 = bitzero, 28 = bitzero, 29 = bitzero, 30 = bitzero  ] as instr)) =
  BranchConditionaltoLinkRegister  (  instr[19..20] (* BH *), instr[11..15] (* BI *), instr[6..10] (* BO *), instr[31] (* LK *)  ) 

 function clause execute (  BranchConditionaltoLinkRegister  (  BH, BI, BO, LK  )  ) =
  {  {
    if((bit)  mode64bit  ) then  M  :=  0  else  M  :=  32  ;
    if((bit)  (  ~  (  ((  BO  )[  2  ])  ))  ) then  CTR  :=  (  CTR  -  1  )  ;
    ctr_ok  :=  (  ((  BO  )[  2  ])  |  (  (  ((  CTR  )[  M  ..  63  ])  !=  0  )  ^  ((  BO  )[  3  ])  )  )  ;
    cond_ok  :=  (  ((  BO  )[  0  ])  |  (  ((  CR  )[  (  BI  +  32  )  ])  ^  (  ~  (  ((  BO  )[  1  ])  ))  )  )  ;
    if((bit)  (  ctr_ok  &  cond_ok  )  ) then  NIA  :=  (  ((  LR  )[  0  ..  61  ])  :  0b00  )  ;
    if((bit)  LK  ) then  LR  :=  (  CIA  +  4  )  ;
  }  } 


 union ast member  (  bit [ 16 ] (* D *) , bit [ 5 ] (* RA *) , bit [ 5 ] (* RT *)  )  LoadWordandZero 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitzero, 4 = bitzero, 5 = bitzero  ] as instr)) =
  LoadWordandZero  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RT *)  ) 

 function clause execute (  LoadWordandZero  (  D, RA, RT  )  ) =
  {  (bit[64]) EA := 0;  (bit[64]) b := 0;  {
    if((bit)  (  RA  ==  0  )  ) then  b  :=  0  else  b  :=  (GPR[  RA  ])  ;
    EA  :=  (  b  +  (  exts  (  D  ))  )  ;
    GPR[  RT  ]  :=  (  0b00000000000000000000000000000000  :  MEM(  EA  ,   4  )  )  ;
  }  } 


 union ast member  (  bit [ 16 ] (* D *) , bit [ 5 ] (* RA *) , bit [ 5 ] (* RS *)  )  StoreWord 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitone, 4 = bitzero, 5 = bitzero  ] as instr)) =
  StoreWord  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 

 function clause execute (  StoreWord  (  D, RA, RS  )  ) =
  {  (bit[64]) EA := 0;  (bit[64]) b := 0;  {
    if((bit)  (  RA  ==  0  )  ) then  b  :=  0  else  b  :=  (GPR[  RA  ])  ;
    EA  :=  (  b  +  (  exts  (  D  ))  )  ;
    MEM(  EA  ,   4  )  :=  ((  (GPR[  RS  ])  )[  32  ..  63  ])  ;
  }  } 


 union ast member  (  bit [ 16 ] (* D *) , bit [ 5 ] (* RA *) , bit [ 5 ] (* RS *)  )  StoreWordwithUpdate 

 function clause decode (([  0 = bitone, 1 = bitzero, 2 = bitzero, 3 = bitone, 4 = bitzero, 5 = bitone  ] as instr)) =
  StoreWordwithUpdate  (  instr[16..31] (* D *), instr[11..15] (* RA *), instr[6..10] (* RS *)  ) 

 function clause execute (  StoreWordwithUpdate  (  D, RA, RS  )  ) =
  {  (bit[64]) EA := 0;  {
    EA  :=  (  (GPR[  RA  ])  +  (  exts  (  D  ))  )  ;
    MEM(  EA  ,   4  )  :=  ((  (GPR[  RS  ])  )[  32  ..  63  ])  ;
    GPR[  RA  ]  :=  EA  ;
  }  } 


 union ast member  (  bit [ 5 ] (* RA *) , bit [ 5 ] (* RT *) , bit [ 16 ] (* SI *)  )  AddImmediate 

 function clause decode (([  0 = bitzero, 1 = bitzero, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitzero  ] as instr)) =
  AddImmediate  (  instr[11..15] (* RA *), instr[6..10] (* RT *), instr[16..31] (* SI *)  ) 

 function clause execute (  AddImmediate  (  RA, RT, SI  )  ) =
  {  {
    if((bit)  (  RA  ==  0  )  ) then  GPR[  RT  ]  :=  (  exts  (  SI  ))  else  GPR[  RT  ]  :=  (  (GPR[  RA  ])  +  (  exts  (  SI  ))  )  ;
  }  } 


 union ast member  (  bit [ 5 ] (* RA *) , bit [ 5 ] (* RB *) , bit [ 5 ] (* RS *) , bit (* Rc *)  )  OR 

 function clause decode (([  0 = bitzero, 1 = bitone, 2 = bitone, 3 = bitone, 4 = bitone, 5 = bitone, 21 = bitzero, 22 = bitone, 23 = bitone, 24 = bitzero, 25 = bitone, 26 = bitone, 27 = bitone, 28 = bitone, 29 = bitzero, 30 = bitzero  ] as instr)) =
  OR  (  instr[11..15] (* RA *), instr[16..20] (* RB *), instr[6..10] (* RS *), instr[31] (* Rc *)  ) 

 function clause execute (  OR  (  RA, RB, RS, Rc  )  ) =
  {  GPR[  RA  ]  :=  (  (GPR[  RS  ])  |  (GPR[  RB  ])  )  } 



end decode
end execute
end ast


register ast instr (* monitor decoded instructions *)

(* fetch-decode-execute cycle *)
function unit cycle () = {
  NIA := CIA + 4;
  instr := decode(MEM(CIA, 4));
  execute(instr);
  CIA := NIA;
}
