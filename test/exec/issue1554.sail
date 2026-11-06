default Order dec
$include <prelude.sail>

register mstatus : bits(3)

function exception_handler (x : bool, b : bits(2)) -> unit = {
  match b {
    0b00 => mstatus = 0b011,
    0b01 => {
      mstatus = 0b000;
      mstatus = [ mstatus with 1 .. 0 = if x then 0b10 else 0b01 ];
    },

    _ => exit(),
  };
}

function main() -> unit = {
  mstatus = 0b000;
  print_bits("mstatus = ", mstatus);
  exception_handler(false, 0b00);
  print_bits("mstatus = ", mstatus);
}
