default Order dec

$include <prelude.sail>

enum E = {
    /// Documentation comment
    /* line comment */ $[attr "Some argument"]
    A,

    /// Another doc comment
      // with a regular comment
  B,
}

scattered enum SE

/// Documentation comment on clause
$[another_attr]
enum clause SE = /* comment */ C

end SE
