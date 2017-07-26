val forall Num 'n, Num 'm, Order 'ord, Type 'a. vector<'n,'m,'ord,'a> -> [:'n:] effect pure vector_start_index

function forall Num 'n, Num 'm, Order 'ord, Type 'a. [:'n:] vector_start_index ((vector<'n,'m,'ord,'a>) vec) =
{
  sizeof 'n
}

function int test ((vector<47,11,dec,bit>) vec) =
{
  vector_start_index(vec)
}

