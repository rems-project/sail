
let _ : unit = match () {
  () => (),
  $[attr] (_ => ()),
  $[attr1] $[attr2] (_ => () /* comment */),
  $[attr1] ($[attr2] (_ => ())) // comment
}
