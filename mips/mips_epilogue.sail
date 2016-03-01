
union ast member unit RI
function clause decode _ = Some(RI)
function clause execute (RI) =
      exit (SignalException (ResI))

end decode
end execute
end ast

function option<ast> supported_instructions (instr) = Some(instr)
