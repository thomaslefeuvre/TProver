open Core.Std
open Literal

include Literal.Set

let neg_all cl = map ~f:Literal.neg cl

let is_all_neg cl = Pervasives.(=) (length (filter ~f:(function (Pos,_) -> true | _ -> false) cl)) 0

let is_unit cl = Pervasives.(=) (length cl) 1

let tautology cl = Pervasives.(<>) (length (inter cl (neg_all cl))) 0

let split cl =
  let literal_list = to_list cl in
  let rec aux ll pos neg =
    match ll with
    | (Pos,x)::ls -> aux ls ((Pos,x)::pos) neg
    | (Neg,y)::ls -> aux ls pos ((Neg,y)::neg)
    | [] -> (of_list pos, of_list neg)
  in aux literal_list [] []

let to_string cl =
	let str_map = List.map ~f:Literal.to_string (to_list cl) in
	let joined = String.concat ~sep:", " str_map in
	"{" ^ joined ^ "}"
