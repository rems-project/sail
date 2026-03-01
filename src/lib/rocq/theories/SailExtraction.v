Require Extraction.

Set Extraction KeepSingleton.
Set Extraction Output Directory ".".

Require Import Bit.
Require Import Ast.
Require Import Value_type.
Require Import AstInduction.
Require Import IdUtil.
Require Import Semantics.
Require Import PatternMatch.

Extraction Blacklist Nat List String.

Separate Extraction Primops l attribute_data BitList.to_hex_digits def impldef opt_default Semantics.Make IdMap.
