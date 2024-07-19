function f b = if b == bitone then bitzero else bitone
function f b = if b == bitone then { bitzero } else { bitone }
function f b = if b == bitone then { let a = 1;bitzero } else { bitone }

function f b = if b == bitone then {  {bitzero } } else { bitone }
function f b = if b == bitone then {  {{bitzero} } } else { bitone }
function f b = if b == bitone then { { let a = 1; bitzero } } else { bitone }
function f b = if b == bitone then { { {let a = 1; bitzero} } } else { bitone }
function f b = if b == bitone then { { { {let a = 1; bitzero}} } } else { {{{let a= 1; bitone}}} }
function f b = if b == bitone then { { { {let a = 1; bitzero}} } } else { {{bitone }}}
function f b = if b == bitone then { { { {let a = 1; bitzero}} } } else { {let a = 1;{bitone }}}

 /* comment */
function/* comment */f b = if b == bitone then bitzero else bitone
function f/* comment */b = if b == bitone then bitzero else bitone
function f b/* comment */= if b == bitone then bitzero else bitone
function f b = /* comment */if b == bitone then bitzero else bitone
// TODO function f b =/* comment */if b == bitone then bitzero else bitone
function f b = if/* comment */b == bitone then bitzero else bitone
function f b = if b/* comment */== bitone then bitzero else bitone
function f b = if b == /* comment */ bitone then bitzero else bitone
// TODO function f b = if b ==/* comment */bitone then bitzero else bitone
function f b = if b == bitone/* comment */then bitzero else bitone
function f b = if b == bitone then/* comment */bitzero else bitone
function f b = if b == bitone then bitzero/* comment */else bitone
function f b = if b == bitone then bitzero else/* comment */bitone
function f b = if b == bitone then bitzero else bitone/* comment */
