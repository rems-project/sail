register (bit) SAT

val forall Nat 'n, Nat 'm, 'n <= 0, 0 <= 'm.
  (nat, [|'n|], [|'m|]) -> [|'n:'m|] effect { wreg } Clamp

function
  forall Nat 'n, Nat 'm, 'n <= 0, 0 <= 'm. ([|'n:'m|])
  Clamp((nat) x, ([|'n|]) y, ([|'m|]) z) = {
    ([|'n:'m|]) result := 0;
    if (x<y) then {
      result := y;
      SAT := bitone;
    } else if (x > z) then {
      result := z;
      SAT := bitone;
    } else {
      result := x;
    };
    result;
  }

