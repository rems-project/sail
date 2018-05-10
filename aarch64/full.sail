
// Prelude
$include "prelude.sail"

// Specification
$include "full/spec.sail"

// Decoder
$include "decode_start.sail"
$include "full/decode.sail"
$include "decode_end.sail"

// Top level loop
$include "main.sail"
