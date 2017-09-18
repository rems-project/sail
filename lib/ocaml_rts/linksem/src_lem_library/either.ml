type ('a, 'b) either = 
  | Left of 'a
  | Right of 'b

let either_case fa fb x = match x with
  | (Left a) -> fa a
  | (Right b) -> fb b

let eitherEqualBy eql eqr (left: ('a, 'b) either) (right: ('a, 'b) either) =  
  match (left, right) with
    | ((Left l), (Left l')) -> eql l l'
    | ((Right r), (Right r')) -> eqr r r'
    | _ -> false
  
let rec either_partition l = ((match l with
  | [] -> ([], [])
  | x :: xs -> begin
      let (ll, rl) = (either_partition xs) in
      (match x with 
        | (Left l) -> ((l::ll), rl)
        | (Right r) -> (ll, (r::rl))
      )
    end
))
