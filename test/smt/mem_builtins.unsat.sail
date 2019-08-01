default Order dec

$include <prelude.sail>
$include <regfp.sail>

$property
function prop() -> bool = {
  __barrier(Barrier_DSB(A64_FullShare, A64_barrier_all));
  let _ = __excl_res();
  __write_mem_ea(Write_exclusive_release, 32, 0xFFFF_FFFF, 8);
  true
}
