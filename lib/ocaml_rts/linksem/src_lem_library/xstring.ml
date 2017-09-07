let explode s = 
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let implode l = 
  let res = String.create (List.length l) in
  let rec imp i = function
  | [] -> res
  | c :: l -> res.[i] <- c; imp (i + 1) l in
  imp 0 l;;

let string_case s c_empty c_cons = begin
  let len = String.length s in
  if (len = 0) then c_empty else
  c_cons (String.get s 0) (String.sub s 1 (len - 1))
end;;

let cons_string c s = begin
  let cs = String.make 1 c in
  cs ^ s
end;;
