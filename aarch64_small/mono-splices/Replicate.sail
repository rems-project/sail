function Replicate(N, x) = {
  assert(N % 'M == 0, "((N MOD M) == 0)");
  let 'O = N / 'M;
  assert(constraint('O * 'M == 'N));
  return(replicate_bits(x, N / 'M))
}
