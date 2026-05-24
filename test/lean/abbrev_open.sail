default Order dec

$include <prelude.sail>

type datasize = {32, 64}

type xlen('N) = range(0, 'N)

enum Color = Red | Green | Blue

union Shape = {
  Circle : int,
  Square : int,
}
