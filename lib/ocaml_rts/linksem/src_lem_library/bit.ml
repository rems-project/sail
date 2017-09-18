type bit = Zero | One

let to_bool b = match b with | Zero -> false | _ -> true
let bn b = match b with | Zero -> One | One -> Zero
let bor b1 b2 = match (b1,b2) with
  | Zero,Zero -> Zero
  | _ -> One
let xor b1 b2 = match (b1,b2) with
  | Zero,Zero -> Zero
  | Zero,One | One,Zero -> One
  | _ -> Zero
let band b1 b2 = match (b1,b2) with
  | One,One -> One
  | _ -> Zero

let add b1 b2 = match (b1,b2) with
  | Zero,Zero -> Zero, false
  | Zero,One | One,Zero -> One, false
  | One,One -> Zero, true
