
typedef vecsyn = vector<0,1,dec,bit>

val cast vector<1,1,dec,bit> -> vector<0,1,dec,bit> effect pure adjust_dec

val vector<1,1,dec,bit> -> vecsyn effect pure test

function test x = x
