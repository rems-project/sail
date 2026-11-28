default Order dec

union Tree('a) = {
  Leaf : 'a,
  Node : (Tree('a), Tree('a)),
}

union S = { S : Tree(S) }
