let rec string_of_list sep string_of = function
  | [] -> ""
  | [x] -> string_of x
  | x::ls -> (string_of x) ^ sep ^ (string_of_list sep string_of ls)

let rec zip xs ys = match (xs,ys) with
  | ([],_) -> []
  | (_, []) -> []
  | (x::xs,y::ys) -> (x,y)::(zip xs ys)

let rec unzip xys = match xys with
  | [] -> ([],[])
  | (x,y)::xys -> let (xs,ys) = unzip xys in (x::xs,y::ys)


let rec unzip3 xyzs = match xyzs with
  | [] -> ([],[],[])
  | (x,y,z)::xyzs -> let (xs,ys,zs) = unzip3 xyzs in (x::xs,y::ys,z::zs)

let explode s = 
  let rec f i  = let c = String.get s i  in match i with
      | 0 -> [ c ] 
      | n -> (f (n-1) @ [ c ] )
  in f (String.length s - 1)

                                                                                                          
(* Implode list of chars into a string *)
let implode s = String.init (List.length s) (fun i -> List.nth s i)

let map_concat f xs = List.concat (List.map f xs)
