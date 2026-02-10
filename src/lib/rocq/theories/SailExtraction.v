Require Extraction.

Set Extraction KeepSingleton.
Set Extraction Output Directory ".".

Require Import Bit.
Require Import Ast.
Require Import Value_type.
Require Import AstInduction.
Require Import IdUtil.
Require Import Semantics.

Extraction Blacklist Nat List String.

Separate Extraction Primops l attribute_data hex_digits_of_bitlist def impldef opt_default Make IdMap.
