
// Prelude
$include "prelude.sail"
$include "no_devices.sail"

// Specification
$include "full/spec.sail"

// Decoder
$include "decode_start.sail"
$include "full/decode.sail"
$include "decode_end.sail"

// Top level loop
$include "main.sail"
