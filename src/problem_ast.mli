
type formula =
  | Iff of formula * formula
  | Imp of formula * formula
  | Or of formula * formula
  | And of formula * formula
  | Not of formula
  | Atom of string
  | True
  | False
  | BadOp of int

val pretty_string : formula -> string
val ugly_string   : formula -> string

(* reduction - ocaml-tptp ast to ours *)
val reduce_atom : Tptp_ast.atom -> formula
val reduce_formula : Tptp_ast.formula -> formula

val simplify : bool -> formula -> formula

val negate : formula -> formula
