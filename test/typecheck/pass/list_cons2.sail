function list<int> foo ((int) i, (list<int>) l) = i :: l

function list<int> bar () = [||||]

function list<int> baz ((list<int>) l) = l

function list<int> quux () = baz ([||||])
