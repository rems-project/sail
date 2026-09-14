

type regidx_range('n) = 'n <= 1 & 'n >= 0

newtype regidx('n), regidx_range('n) = Regidx : int('n)

type s_regidx = { 'n, regidx_range('n) . regidx('n) }

mapping int_string : int <-> string = {
  0 <-> "0",
  1 <-> "1",
}

mapping encdec_reg : s_regidx <-> string = { 
  Regidx(r) <-> int_string(r),
}
