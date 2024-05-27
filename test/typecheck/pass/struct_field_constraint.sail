default Order dec

$include <prelude.sail>

type constrained_range('v), 'v in {10, 20, 30} =
  range(0, if 'v == 10 then 1 else if 'v == 20 then 2 else 3)

struct test('v : Int), 'v in {10, 20, 30} = {
  crange : constrained_range('v),
}
