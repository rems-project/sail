`ifndef SAIL_LIBRARY
`define SAIL_LIBRARY

// The Sail unit type.
typedef enum logic [0:0] {SAIL_UNIT=0} sail_unit;

function automatic sail_unit sail_print_endline(string s);
   $display(s);
   return SAIL_UNIT;
endfunction // sail_print_endline

function automatic sail_unit sail_prerr_endline(string s);
   $display(s);
   return SAIL_UNIT;
endfunction // sail_prerr_endline

function automatic sail_unit sail_print(string s);
   $write(s);
   return SAIL_UNIT;
endfunction // sail_print

function automatic sail_unit sail_prerr(string s);
   $write(s);
   return SAIL_UNIT;
endfunction // sail_prerr

function automatic sail_unit sail_assert(bit b, string msg);
   if (!b) begin
      $display("%s", msg);
   end
endfunction // sail_assert

function automatic bit sail_eq_string(string s1, string s2);
   return s1 == s2;
endfunction

bit [7:0] sail_memory [63:0];

`endif //  `ifndef SAIL_LIBRARY
