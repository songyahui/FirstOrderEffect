effect Found : (int * int list) -> int list  


let rec take lst n 
  (*@ requires true, emp @*)
  (*@ ensures  true, emp \/ Found @*)
= 
  match lst with
  | [] -> []
  | first :: rest ->
  if n = 0 then
    perform (Found (first, rest))
  else first :: (take rest (n - 1))
  
let handler lst n 
  (*@ requires true, emp @*)
  (*@ ensures  true, emp \/ Found @*)
=
  match take lst n with
  | li -> li 
  | effect (Found (first,  rest)) k -> first :: continue k rest

let main = 
  let list = handler [1;2;3;4;0] 3 in 
  print_string (List.fold_left (fun acc a -> acc ^ " " ^ string_of_int a) "" list ^ "\n")
