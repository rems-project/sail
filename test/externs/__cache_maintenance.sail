default Order dec

$include <prelude.sail>
$include <regfp.sail>

// Test for the __cache_maintenance primitive
function main() -> unit = {
  __cache_maintenance(Cache_op_D_IVAC, 64, 0x0000_0000_8000_0000);
}
