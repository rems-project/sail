default Order dec

scattered union ast('datasize : Int, 'destsize : Int, 'regsize : Int)

val execute : forall ('datasize : Int) ('destsize : Int) ('regsize : Int).
  ast('datasize, 'destsize, 'regsize) -> unit

scattered function execute

union clause ast = test : (vector(8, dec, bit), vector('regsize, dec, bit))

function clause execute test(x, y) = return(())

union clause ast = test2 : int

function clause execute test2(_) = return(())

end execute
end ast