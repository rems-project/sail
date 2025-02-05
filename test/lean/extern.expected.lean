import Out.Sail.Sail

def extern_add : Int :=
  (HAdd.hAdd 5 4)

def extern_sub : Int :=
  (HSub.hSub 5 4)

def extern_sub_nat : Nat :=
  (HSub.hSub 5 4)

def extern_negate : Int :=
  (Neg.neg 5)

def extern_mult : Int :=
  (HMul.hMul 5 4)

def extern_tdiv : Int :=
  (Int.tdiv 5 4)

def extern_tmod : Int :=
  (Int.tmod 5 4)

def extern_tmod_positive : Int :=
  (Int.tmod 5 4)

def extern_max : Int :=
  (Max.max 5 4)

def extern_min : Int :=
  (Min.min 5 4)

def extern_abs_int_plain : Int :=
  let x := -5
  (Sail.Int.intAbs x)

def extern_eq_unit : Bool :=
  (Eq () ())

def extern_eq_bit : Bool :=
  (Eq 0#1 1#1)

def extern_not : Bool :=
  (Bool.not true)

def extern_and : Bool :=
  (Bool.and true false)

def extern_and_no_flow : Bool :=
  (Bool.and true false)

def extern_or : Bool :=
  (Bool.or true false)

def extern_eq_bool : Bool :=
  (Eq true false)

def extern_eq_int : Bool :=
  (Eq 5 4)

def extern_lteq_int : Bool :=
  (LE.le 5 4)

def extern_gteq_int : Bool :=
  (GE.ge 5 4)

def extern_lt_int : Bool :=
  (LT.lt 5 4)

def extern_gt_int : Bool :=
  (GT.gt 5 4)

def extern_eq_anything : Bool :=
  (BEq.beq true true)

def initialize_registers : Unit :=
  ()

