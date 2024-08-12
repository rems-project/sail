`ifndef SAIL_LIBRARY_MODULES
`define SAIL_LIBRARY_MODULES

// The Sail unit type.
typedef enum logic [0:0] {SAIL_UNIT=0} sail_unit;

// The Sail zero-width bitvector.
typedef enum logic [0:0] {SAIL_ZWBV=0} sail_zwbv;

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
endmodule // print_endline

function automatic bit sail_valid_hex_bits(int n, string hex);
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
      if (!((c >= 49 && c <= 57) || (c >= 65 && c <= 70) || (c >= 97 && c <= 102))) return 1'h0;
   end;

   return 1'h1;
endfunction // sail_valid_hex_bits

function automatic string sail_string_take(string str, int n);
   return str.substr(0, n - 1);
endfunction // sail_string_take

`endif
