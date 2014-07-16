 typedef xer = register bits [ 0 : 63 ] {
  32 : SO;
  33 : OV;
  34 : CA;
  35..36: FOOBAR;
 }

register (xer) XER
register (bit) query

register alias CA = XER.CA
register alias Fo = XER[35]
register alias foobar = XER[35..36]
register alias doub = XER:XER

function (bit[64]) main _ = {
  XER := 0b0101010101010101010101010101010101010101010101010101010101010010;
  f := XER;
  (bit[7]) foo := XER[57..63];
  query := XER.SO;
  XER.SO := 0;
  query := CA;
  query := Fo;
  CA := query;
  XER.FOOBAR := 0b11;
  XER.FOOBAR := foobar;
  query := doub[13];
  XER }

