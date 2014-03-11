 typedef xer = register bits [ 0 : 63 ] {
  32 : SO;
  33 : OV;
  34 : CA;
 }

register (xer) XER
register (bit[1]) query

function bit main _ = {
  XER := 0b010101010101010101010101010101010101010101010101010101010101001;
  f := XER;
  (bit[7]) foo := XER[57..63];
  query := XER.SO;
  (*XER.SO := query;*)
  bitzero }

