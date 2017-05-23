default Order dec

val forall Nat 'W, 'W IN {8,16,32,64,128}. bit['W] -> bit['W] effect pure BigEndianReverse

function rec forall Nat 'W, 'W IN {8, 16, 32, 64, 128}. bit['W] BigEndianReverse ((bit['W]) value) =
{
    (nat) width := length(value);
    (nat) half := width quot 2;
    if width == 8 then value
    else BigEndianReverse(value[(half - 1)..0]) : BigEndianReverse(value[(width - 1)..half]);
}
