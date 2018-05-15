$include "prelude.sail"

val "zero_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)

register _UART_ADDR : bits(52)

val initialize_uart : bits(52) -> unit effect {wreg}

function initialize_uart(base_address) = {
  _UART_ADDR = base_address;
}

register UARTDR    : bits(12)
register UARTRSR   : bits(4)
register UARTFR    : bits(9)
register UARTILPR  : bits(8)
register UARTIBRD  : bits(16)
register UARTFBRD  : bits(6)
register UARTLCR_H : bits(8)
register UARTCR    : bits(16)
register UARTIFLS  : bits(6)
register UARTIMSC  : bits(11)
register UARTRIS   : bits(11)
register UARTMIS   : bits(11)

/* write only, so implement as function? */
val UARTICR : bits(11) -> unit
function UARTICR(b) = () /* TODO */

register UARTDMACR : bits(3)

val write_uart : forall 'n, 0 <= 'n <= 32. (bits(12), bits('n)) -> unit effect {escape, wreg}

function write_uart(offset, data) = {
  let data = zero_extend(data, 32);
  match offset {
    0x000 => UARTDR    = data[0, 12],
    0x004 => UARTRSR   = data[0, 4],
    /* 0x008 - 0x014 Reserved */
    /* 0x018 UARTFR read only */
    /* 0x01C Reserved */
    0x020 => UARTILPR  = data[0, 8],
    0x024 => UARTIBRD  = data[0, 16],
    0x028 => UARTFBRD  = data[0, 6],
    0x02C => UARTLCR_H = data[0, 8],
    0x030 => UARTCR    = data[0, 16],
    0x034 => UARTIFLS  = data[0, 6],
    0x038 => UARTIMSC  = data[0, 11],
    /* 0x03C UARTRIS read only */
    /* 0x040 UARTMIS read only */
    0x044 => UARTICR() = data[0, 11],
    0x048 => UARTDMACR = data[0, 3],

    _ => throw(Error_Undefined())
  }
}

val read_uart : bits(12) -> bits(32) effect {escape, rreg}

function read_uart(offset) = {
  let data : {'n, 0 <= 'n <= 32. bits('n)} = match offset {
    0x000 => UARTDR,
    0x004 => UARTRSR,
    /* 0x008 - 0x014 Reserved */
    0x018 => UARTFR,
    /* 0x01C Reserved */
    0x020 => UARTILPR,
    0x024 => UARTIBRD,
    0x028 => UARTFBRD,
    0x02C => UARTLCR_H,
    0x030 => UARTCR,
    0x034 => UARTIFLS,
    0x038 => UARTIMSC,
    0x03C => UARTRIS,
    0x040 => UARTMIS,
    /* 0x044 UARTICR write only */
    0x048 => UARTDMACR,

    _ => throw(Error_Undefined())
  };
  zero_extend(data, 32)
}

val reset_uart : unit -> unit effect {wreg, undef}

function reset_uart() = {
  UARTDR    = undefined;
  UARTRSR   = 0x0;
  UARTFR    = undefined : bits(1) @ 0b10010 @ undefined : bits(3);
  UARTILPR  = 0x00;
  UARTIBRD  = 0x0000;
  UARTFBRD  = 0b00_0000;
  UARTLCR_H = 0x00;
  UARTCR    = 0x0300;
  UARTIFLS  = 0b01 @ 0x2;
  UARTIMSC  = 0b000_0000_0000;
  UARTRIS   = 0x00 @ undefined : bits(3);
  UARTMIS   = 0x00 @ undefined : bits(3);
  UARTDMACR = 0b000
}