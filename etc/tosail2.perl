#!/usr/bin/env perl

use strict;
my $in_enum = 0;
my $in_bitfield = 0;

while (<>) {
	my $line = $_;

	# fix bitfield declaration, assumes zero based
	if (s/typedef\s+(\w+)\s+=\s+register\s+bits\s+\[\s*([\d]+)\s*:\s*0\s*\]/bitfield $1 : bits(@{[$2 + 1]}) =/) {
		$in_bitfield = 1;
	}
	if ($in_bitfield) {
		if (/\}/) { $in_bitfield = 0; }
		# fix fields of bitfields
		s!(\d+)\s*(\.\.\s*\d+)?\s*:\s*(\w+\s*);!$3 : $1$2,!;
	}
	# sail2 does not have != at all
	s!:=!=!;
	# fix comment style
	s!\(\*!\/\*!g;
	s!\*\)!\*\/!g;
	# fix register declarations
	s!register \(([^\)]+)\)\W+(\w+)!register $2 : $1!;

	# fix enumerations.
	if (s!typedef\s+(\w+)\s+=\s+enumerate!enum $1 =!) {
		$in_enum = 1;
	}
	if ($in_enum) {
		s/;/,/g;
		if (/\}/) {$in_enum = 0};
	}

	# fix type aliases
	s!typedef\s+(\w+)\s+=\s+(.*)!type $1 = $2!;

	# fix switch -> match
	s!switch\s*\((.*)\)!match $1!;
	# fix switch cases, need to add commas at end of lines
	s!case\s+(.*)->!$1 =>!;

	# fix lets with type
	s!let \(([^\)]+)\)\W+(\w+)!let $2 : $1!;

	# fix val declarations
	s!val (.*) (\w+)!val $2 : $1!;

	# attempt to decode pattern matches
	if (/clause decode/) {
		s/:/@/g;
		s!\((\w+)\) (\w+)!$2 : $1!g;
	}

        # fix scattered union declaration
        s!scattered\s+type\s+(\w+)\s+=\s+const\s+union!scattered union $1!;
        
        # fix scattered union members
        s!union\s+(\w+)\s+member\s+(\w+)\s+(\w+)!union clause $1 = $3 : $2!;

        # fix scattered function declaration (drops type, assumes separate val dec.)
        s!scattered\s+function\s+([^\s]+)\s+(\w+)!scattered function $2!;
        
	# fix any bits[n]
	s!bit\s*\[([^\]]+)\]!bits\($1\)!g;

	# fix option types
	s!option<([^>]+)>!option($1)!;

        # drop extern, Nat?
	print;
}
