import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

noncomputable section

abbrev real := ℝ

-- val "neg_real" : real -> real
def neg_real (x : real) : real := -x

-- val "mult_real" : (real, real) -> real
def mult_real (x y : real) : real := x * y

-- val "sub_real" : (real, real) -> real
def sub_real (x y : real) : real := x - y

-- val "add_real" : (real, real) -> real
def add_real (x y : real) : real := x + y

-- val "div_real" : (real, real) -> real
def div_real (x y : real) : real := x / y

-- val sqrt = pure "sqrt_real" : real -> real
def sqrt_real (x : real) : real := Real.sqrt x

-- val "abs_real" : real -> real
def abs_real (x : real) : real := |x|

-- val floor = pure "round_down" : real -> int
def round_down (x : real) : Int := ⌊x⌋

-- val ceil = pure "round_up" : real -> int
def round_up (x : real) : Int := ⌈x⌉

-- val "to_real" : int -> real
def to_real (x : Int) : real := x

-- val "eq_real" : (real, real) -> bool
def eq_real (x y : real) : Bool := x = y

-- val "lt_real" : (real, real) -> bool
def lt_real (x y : real) : Bool := x < y

-- val "gt_real" : (real, real) -> bool
def gt_real (x y : real) : Bool := x > y

-- val "lteq_real" : (real, real) -> bool
def lteq_real (x y : real) : Bool := x ≤ y

-- val "gteq_real" : (real, real) -> bool
def gteq_real (x y : real) : Bool := x ≥ y

-- val pow_real = pure "real_power" : (real, int) -> real
def pow_real (x : real) (n : Int) : real := x ^ n

-- val "print_real" : (string, real) -> unit
def print_real (_ : String) (_ : real) : Unit := ()

-- val "prerr_real" : (string, real) -> unit
def prerr_real (_ : String) (_ : real) : Unit := ()

-- val "random_real" : unit -> real
def random_real (_ : Unit) : real := 34
