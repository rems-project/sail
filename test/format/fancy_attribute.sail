
/// Doc comment
$[test {
  key = """
    multi-line string
      in
    attribute\n
    """,
  // here
  "small object" = { n = 3 },
  foo = /* weird comment place */ "bar",
  "" = "",
  some_number = 4 // trailing comment
}]
$[empty_object {}]
let x : int = $[attr "foo"] 5
