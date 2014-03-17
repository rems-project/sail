 typedef xer = register bits [ 0 : 63 ] {
  32 : SO;
  33 : OV;
  34 : CA;
  35..36: FOOBAR;
 }

register (xer) XER
register (bit) query

function (bit[64]) main _ = {
  XER := 0b010101010101010101010101010101010101010101010101010101010101001;
  f := XER;
  (bit[7]) foo := XER[57..63];
  query := XER.SO;
  XER.SO := 0;
  XER.FOOBAR := 0b11;
  XER }

