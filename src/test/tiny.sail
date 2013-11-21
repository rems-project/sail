
(* is the following typedef equivalent to this?
  typedef regT = bit[7]
do you want/need something like this instead?
  typedef regT = register bits [0:6] { 0..6: regT }
*)

typedef regT  = bit[0..6]
typedef wordT = bit[0..31]
typedef immT  = bit[0..23]
typedef addrT = bit[0..9]
typedef memT  = addrT -> wordT { wmem, rmem }

(* exception Reserved -- no support for exceptions (yet?) *)

(* beware: L3 has "construct", and we have "const struct", but the
   equivalent of "construct" is either "const union" or "enumerate" *)

typedef funcT = enumerate {fADD; fSUB; fINC; fDEC; fAND; fOR; fXOR; fReserved} 
typedef shiftT  = enumerate {noShift; RCY1; RCY8; RCY16}
typedef conditionT  = enumerate {skipNever; skipNeg; skipZero; skipInRdy}

(* the previous one will convert to/from integers; safer alternative:
typedef funcT = const union { unit fADD; ... }

*)

(****
---------------------------------------------
-- State
---------------------------------------------

declare
{
   PC :: addrT          -- Program Counter
   R :: regT -> wordT   -- Registers
   IM :: memT           -- Instruction Memory
(* not sure the interpreter will recognize rmem through the typedef *)
   DM :: memT           -- Data Memory
   InRdy :: bool        -- Input Ready
   InData :: wordT      -- Input Data
   OutStrobe :: wordT   -- Output Data
}

---------------------------------------------
-- Operations
---------------------------------------------

wordT function (func::funcT, a:: wordT, b:: wordT) =
   match func
   {
     case fADD => a + b
     case fSUB => a - b
     case fINC => b + 1
     case fDEC => b - 1
     case fAND => a && b
     case fOR  => a || b
     case fXOR => a ?? b
     case _ => #Reserved
   }

wordT shifter (shift::shiftT, a::wordT) =
   match shift
   {
      case noShift => a
      case RCY1    => a #>> 1
      case RCY8    => a #>> 8
      case RCY16   => a #>> 16
   }

wordT ALU (func::funcT, shift::shiftT, a::wordT, b::wordT) =
   shifter (shift, function (func, a, b))

unit incPC (skip::conditionT, alu::wordT) =
   match skip
   {
      case skipNever => PC <- PC + 1
      case skipNeg   => PC <- PC + if alu < 0  then 2 else 1
      case skipZero  => PC <- PC + if alu == 0 then 2 else 1
      case skipInRdy => PC <- PC + if InRdy    then 2 else 1
   }

-- Common functionality
unit norm (func::funcT, shift::shiftT, skip::conditionT,
           wback::bool, strobe::bool, w::regT, a::regT, b::regT) =
{
   alu = ALU (func, shift, R(a), R(b));
   when wback do R(w) <- alu;
   when strobe do OutStrobe <- alu;
   incPC (skip, alu)
}

---------------------------------------------
-- Instructions
---------------------------------------------

define Normal (func::funcT, shift::shiftT, skip::conditionT,
               w::regT, a::regT, b::regT) =
   norm (func, shift, skip, true, false, w, a, b)


define StoreDM (func::funcT, shift::shiftT, skip::conditionT,
                w::regT, a::regT, b::regT) =
{
   DM([R(b)]) <- R(a);
   norm (func, shift, skip, true, false, w, a, b)
}

define StoreIM (func::funcT, shift::shiftT, skip::conditionT,
                w::regT, a::regT, b::regT) =
{
   IM([R(b)]) <- R(a);
   norm (func, shift, skip, true, false, w, a, b)
}

define Out (func::funcT, shift::shiftT, skip::conditionT,
            w::regT, a::regT, b::regT) =
   norm (func, shift, skip, true, true, w, a, b)

define LoadDM (func::funcT, shift::shiftT, skip::conditionT,
               w::regT, a::regT, b::regT) =
{
   R(w) <- DM([R(b)]);
   norm (func, shift, skip, false, false, w, a, b)
}

define In (func::funcT, shift::shiftT, skip::conditionT,
           w::regT, a::regT, b::regT) =
{
   R(w) <- InData;
   norm (func, shift, skip, false, false, w, a, b)
}

define Jump (func::funcT, shift::shiftT, w::regT, a::regT, b::regT) =
{
   R(w) <- ZeroExtend (PC + 1);
   PC <- [ALU (func, shift, R(a), R(b))]
}

define LoadConstant (w::regT, imm::immT) =
{
   R(w) <- ZeroExtend (imm);
   PC <- PC + 1
}

define ReservedInstr = #Reserved

define Run

---------------------------------------------
-- Decode
---------------------------------------------

instruction Decode (opc::wordT) =
   match opc
   {
      case 'Rw 1 imm`24' => LoadConstant (Rw, imm)
      case 'Rw 0 Ra Rb Function Shift Skip Op' =>
         {
            func  = [Function :: bits(3)] :: funcT;
            shift = [Shift :: bits(2)] :: shiftT;
            skip  = [Skip :: bits(2)] :: conditionT;
            match Op
            {
               case 0 => Normal (func, shift, skip, Rw, Ra, Rb)
               case 1 => StoreDM (func, shift, skip, Rw, Ra, Rb)
               case 2 => StoreIM (func, shift, skip, Rw, Ra, Rb)
               case 3 => Out (func, shift, skip, Rw, Ra, Rb)
               case 4 => LoadDM (func, shift, skip, Rw, Ra, Rb)
               case 5 => In (func, shift, skip, Rw, Ra, Rb)
               case 6 => Jump (func, shift, Rw, Ra, Rb)
               case 7 => ReservedInstr
            }
         }
   }

---------------------------------------------
-- Next State
---------------------------------------------

unit Next =
{
  i = Decode (IM (PC));
  when i <> ReservedInstr do Run (i)
}

---------------------------------------------
-- Encode
---------------------------------------------

wordT enc
  (args::funcT * shiftT * conditionT * regT * regT * regT, opc::bits(3)) =
{
   func, shift, skip, w, a, b = args;
   return (w : '0' : a : b : [func]`3 : [shift]`2 : [skip]`2 : opc)
}

wordT Encode (i::instruction) =
   match i
   {
      case LoadConstant (Rw, imm) => Rw : '1' : imm
      case Normal (args)  => enc (args, '000')
      case StoreDM (args) => enc (args, '001')
      case StoreIM (args) => enc (args, '010')
      case Out (args)     => enc (args, '011')
      case LoadDM (args)  => enc (args, '100')
      case In (args)      => enc (args, '101')
      case Jump (func, shift, Rw, Ra, Rb) =>
         enc ((func, shift, skipNever, Rw, Ra, Rb), '110')
      case ReservedInstr => 0b111
   }

---------------------------------------------
-- Load into Instruction Memory
---------------------------------------------

unit LoadIM (a::addrT, i::instruction list) measure Length (i) =
   match i
   {
      case Nil => nothing
      case Cons (h, t) =>
        {
           IM(a) <- Encode (h);
           LoadIM (a + 1, t)
        }
   }

*****)
