
typedef Int = exist 'n. [:'n:]

val forall 'n, 'm. ([:'n:], [:'m:]) -> exist 'o, 'o = 'n + 'm. [:'o:] effect pure add

val forall 'n, 'm. ([:'n:], [:'m:]) -> exist 'o, 'o = 'n * 'm. [:'o:] effect pure mult

overload (deinfix +) [add]

overload (deinfix * ) [mult]

let x = 3 + 4

let y = x + x * x

let ([:7 * 8:]) z = y

typedef Range = forall Num 'n, Num 'm, 'n <= 'm. exist 'o, 'n <= 'o & 'o <= 'm. [:'o:]

let (Range<3,4>) a = 3

let (Range<2,5>) b = a + 1