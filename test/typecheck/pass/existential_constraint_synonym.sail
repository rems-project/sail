default Order dec

type X : Int = 32
type regno ('n : Int), 0 <= 'n < X = int('n)
type R = { 'n, 0 <= 'n < X. regno('n) }
