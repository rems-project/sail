
function foo() = {
    if cond
    then 2 /* comment */
    else { 3 /* comment */ }
}

function foo() = {
    if cond
    then 2// comment
    else { 3   // comment
}
}

function foo() = {
    if cond
    then {
      if cond2
      then 2// comment
      else { 4 /* comment */ }}
    else { 3   // comment
}
}
