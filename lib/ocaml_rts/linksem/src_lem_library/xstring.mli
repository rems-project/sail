val explode : string -> char list
val implode : char list -> string
val cons_string : char -> string -> string
val string_case : string -> 'a -> (char -> string -> 'a) -> 'a
