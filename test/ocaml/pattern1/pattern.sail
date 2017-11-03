val main : unit -> unit

function main () = {
  vec = 0x4F;
  match vec {
    0b01 @ x : bits(2) @ 0xF => if x == 0b00 then print("pass") else print("x is incorrect"),
    _ => print("pattern fail")
  }
}
