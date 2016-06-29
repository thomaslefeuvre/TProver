open Core.Std

type atom = string with sexp, compare

type sign = Pos | Neg with sexp, compare

type t = sign * atom with sexp, compare

include Comparable.Make(struct
  (* ocaml types implicitly recursive so need to
     specify nonrec (otherwise type def cyclic) *)
  type nonrec t = t with sexp, compare
end)

let neg = function
  | (Pos, s) -> (Neg, s)
  | (Neg, s) -> (Pos, s)

let to_string = function
  | (Pos, s) -> s
  | (Neg, s) -> "¬"^s
