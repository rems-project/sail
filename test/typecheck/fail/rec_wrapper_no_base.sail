default Order dec

struct Identity('a) = { ident : 'a }

union Seq = { Seq : Identity(Seq) }
