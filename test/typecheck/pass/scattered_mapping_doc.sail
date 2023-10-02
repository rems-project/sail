default Order dec

$include <prelude.sail>

enum E = A | B | C

/*! Documentation
 * comment
 * with
 * asterisks
 */
val foo : E <-> int

scattered mapping foo

/*! Mapping clause doc comment /* nested */ */
mapping clause foo = A <-> 3

/*! Mapping clause
 * box style
 * comment */
mapping clause foo = B <-> 2

$[some_attribute]
mapping clause foo = C <-> 1
