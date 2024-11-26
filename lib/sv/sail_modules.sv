`ifndef SAIL_LIBRARY_MODULES
`define SAIL_LIBRARY_MODULES

// The Sail unit type.
typedef enum logic [0:0] {SAIL_UNIT=0} sail_unit;

// The Sail zero-width bitvector.
typedef enum logic [0:0] {SAIL_ZWBV=0} sail_zwbv;

int cycle_count;

function automatic int get_cycle_count(sail_unit u);
   return cycle_count;
endfunction

module print
  (input string     in_str,
   input string     in_sail_stdout,
   output sail_unit out_return,
   output string    out_sail_stdout
   );

   always_comb begin
      out_sail_stdout = {in_sail_stdout, in_str};
      out_return = SAIL_UNIT;
   end
endmodule

module print_endline
  (input string     in_str,
   input string     in_sail_stdout,
   output sail_unit out_return,
   output string    out_sail_stdout
   );

   always_comb begin
      out_sail_stdout = {in_sail_stdout, in_str, "\n"};
      out_return = SAIL_UNIT;
   end
endmodule

function automatic bit valid_hex_bits(int n, string hex);
   int  len = hex.len();
   int  non_zero = 2;
   int  fnz_width;
   byte fnz;
   int  hex_width;

   // The string must be prefixed by '0x', and contain at least one character after the '0x'
   if (len < 3) return 1'h0;
   if (hex.substr(0, 1) != "0x") return 1'h0;

   // Ignore any leading zeros
   while (hex[non_zero] == 48 && non_zero < len - 1) begin
      non_zero++;
   end;

   // Check how many bits we need for the first-non-zero (fnz) character.
   fnz = hex[non_zero];
   if (fnz == 48) fnz_width = 0;
   else if (fnz == 49) fnz_width = 1;
   else if (fnz >= 50 && fnz <= 51) fnz_width = 2;
   else if (fnz >= 52 && fnz <= 55) fnz_width = 3;
   else fnz_width = 4;

   hex_width = fnz_width + ((len - (non_zero + 1)) * 4);
   if (n < hex_width) return 1'h0;

   for (int i = non_zero; i < len; i++) begin
      byte c = hex[i];
      if (!((c >= 48 && c <= 57) || (c >= 65 && c <= 70) || (c >= 97 && c <= 102))) return 1'h0;
   end;

   return 1'h1;
endfunction // valid_hex_bits

function automatic sail_bits parse_hex_bits(int n, string str);
   logic [SAIL_BITS_WIDTH-1:0] buffer;
   logic [SAIL_BITS_WIDTH-33:0] padding;
   string digits;

   digits = str.substr(2, str.len() - 1);
   padding = 0;
   buffer = {padding, digits.atohex()};

   return '{n[SAIL_INDEX_WIDTH-1:0] * 8, buffer};
endfunction

function automatic string string_take(string str, int n);
   return str.substr(0, n - 1);
endfunction

function automatic string string_drop(string str, int n);
   return str.substr(n, str.len() - 1);
endfunction

function automatic int string_length(string str);
   return str.len();
endfunction

`ifdef SAIL_DPI_MEMORY
import "DPI-C" function bit[7:0] sail_read_byte(logic [63:0] addr);

import "DPI-C" function bit sail_read_tag(logic [63:0] addr);
`else
logic [7:0] sail_memory [logic [63:0]];

bit sail_tag_memory [logic [63:0]];
`endif

typedef struct {
   logic [63:0] paddr;
   logic [7:0]  data;
} sail_write;

typedef sail_write sail_memory_writes [$];

function automatic sail_bits emulator_read_mem(logic [63:0] addrsize, sail_bits addr, sail_int n);
   logic [63:0] paddr;
   logic [SAIL_BITS_WIDTH-1:0] buffer;
   logic [SAIL_INDEX_WIDTH-2:0] i;

   paddr = addr.bits[63:0];

   for (i = n[SAIL_INDEX_WIDTH-2:0]; i > 0; i = i - 1) begin
`ifdef SAIL_DPI_MEMORY
      buffer[7 + ((i - 1) * 8) -: 8] = sail_read_byte(paddr + (64'(i) - 1));
`else
      buffer[7 + ((i - 1) * 8) -: 8] = sail_memory[paddr + (64'(i) - 1)];
`endif
   end

   return '{n[SAIL_INDEX_WIDTH-1:0] * 8, buffer};
endfunction

function automatic sail_bits emulator_read_mem_ifetch(logic [63:0] addrsize, sail_bits addr, sail_int n);
   return emulator_read_mem(addrsize, addr, n);
endfunction

function automatic sail_bits emulator_read_mem_exclusive(logic [63:0] addrsize, sail_bits addr, sail_int n);
   return emulator_read_mem(addrsize, addr, n);
endfunction

function automatic bit emulator_read_tag(logic [63:0] addrsize, sail_bits addr);
   logic [63:0] paddr;
   paddr = addr.bits[63:0];
`ifdef SAIL_DPI_MEMORY
   return sail_read_tag(paddr);
`else
   if (sail_tag_memory.exists(paddr) == 1)
     return sail_tag_memory[paddr];
   else
     return 1'b0;
`endif
endfunction

module emulator_write_mem
  (input  logic [63:0]       addrsize,
   input  sail_bits          addr,
   input  sail_int           n,
   input  sail_bits          value,
   input  sail_memory_writes in_writes,
   output sail_unit          ret,
   output sail_memory_writes out_writes
   );
endmodule

module emulator_write_mem_exclusive
  (input  logic [63:0]       addrsize,
   input  sail_bits          addr,
   input  sail_int           n,
   input  sail_bits          value,
   input  sail_memory_writes in_writes,
   output sail_unit          ret,
   output sail_memory_writes out_writes
   );
endmodule

module emulator_write_tag
  (input  logic [63:0]       addrsize,
   input  sail_bits          addr,
   input  bit                tag_value,
   input  sail_memory_writes in_writes,
   output sail_unit          ret,
   output sail_memory_writes out_writes
   );
endmodule

function automatic string sail_string_of_bits(sail_bits bv);
   return "";
endfunction

`endif
