default Order inc

scattered typedef ast = const union
val ast -> unit effect pure execute
scattered function unit execute

union ast member (unit) DUMMY
function clause execute (DUMMY) = ()

end ast
end execute

function unit test_assert (name, pred) = {
  print (name);
  if pred then
    print (": pass\n")
  else
    print(": fail\n")
}
