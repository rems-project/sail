
// Prelude
$include "prelude.sail"
$include "no_devices.sail"

// Specification
$include "no_vector/spec.sail"

// Decoder
$include "decode_start.sail"
$include "no_vector/decode.sail"
$include "decode_end.sail"

// Top level loop
$include "main.sail"
