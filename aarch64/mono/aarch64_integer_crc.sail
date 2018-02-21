val aarch64_integer_crc : forall ('size : Int).
  (bool, int, int, int, atom('size)) -> unit effect {escape, undef, rreg, wreg}

function aarch64_integer_crc (crc32c, d, m, n, size) = {
  assert(constraint('size in {8,16,32,64}));
  if ~(HaveCRCExt()) then UnallocatedEncoding() else ();
  acc : bits(32) = aget_X(n);
  val_name : bits('size) = aget_X(m);
  poly : bits(32) = __GetSlice_int(32, if crc32c then 517762881 else 79764919, 0);
  tempacc : bits('size + 32) = BitReverse(acc) @ Zeros(size);
  tempval : bits('size + 32) = BitReverse(val_name) @ Zeros(32);
  aset_X(d, BitReverse(Poly32Mod2(tempacc ^ tempval, poly)))
}
