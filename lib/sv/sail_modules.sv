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
endmodule

`endif
