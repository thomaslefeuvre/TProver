open Core.Std
open Tptp_ast

type formula =
  | Iff of formula * formula
  | Imp of formula * formula
  | Or of formula * formula
  | And of formula * formula
  | Not of formula
  | Atom of string
  | True
  | False
  (* use this to represent any problematic formula: *)
  | BadOp of int


(*** PRINTING ***)

let pretty_string f = 
  let rec aux p = function
    | BadOp n -> "*" ^ (string_of_int n)
    | Atom s -> s
    | True -> "t"
    | False -> "f"
    | Not f1 ->
      "¬" ^ (aux 8 f1)
    | And (f1, f2) ->
      let str = (aux 7 f1) ^ " ∧ " ^ (aux 6 f2) in
      if p > 6 then "(" ^ str ^ ")" else str
    | Or (f1, f2) ->
      let str = (aux 5 f1) ^ " ∨ " ^ (aux 4 f2) in
      if p > 4 then "(" ^ str ^ ")" else str
    | Imp (f1, f2) ->
      let str = (aux 3 f1) ^ " → " ^ (aux 2 f2) in
      if p > 2 then "(" ^ str ^ ")" else str
    | Iff (f1, f2) ->
      let str = (aux 1 f1) ^ " ↔ " ^ (aux 0 f2) in
      if p > 0 then "(" ^ str ^ ")" else str
  in aux 0 f

let rec ugly_string = function
  | BadOp n -> "BadOp(" ^ (string_of_int n) ^ ")"
  | True -> "True"
  | False -> "False"
  | Atom x -> x
  | Not f -> "Not(" ^ (ugly_string f) ^ ")"
  | And (f1,f2) -> "And(" ^ (ugly_string f1) ^ "," ^ (ugly_string f2) ^ ")"
  | Or (f1,f2) -> "Or(" ^ (ugly_string f1) ^ "," ^ (ugly_string f2) ^ ")"
  | Imp (f1,f2) -> "Imp(" ^ (ugly_string f1) ^ "," ^ (ugly_string f2) ^ ")"
  | Iff (f1,f2) -> "Iff(" ^ (ugly_string f1) ^ "," ^ (ugly_string f2) ^ ")"


(*** REDUCTION ***)

let reduce_atom = function
  | Equals (_,_) -> BadOp 2
  | Pred (Plain_word w,_) -> Atom w
  | Pred (Defined_word "$true", _) -> True
  | Pred (Defined_word "$false", _) -> False
  | Pred (Defined_word w, _) -> Atom w
  | Pred (System_word w,_) -> Atom w
    
let rec reduce_formula = function
  | Binop (Equiv,f1,f2) -> Iff(reduce_formula f1,reduce_formula f2)
  | Binop (Implies_rev,f1,f2) -> Imp(reduce_formula f2,reduce_formula f1)
  | Binop (Implies,f1,f2) -> Imp(reduce_formula f1,reduce_formula f2)
  | Binop (Or,f1,f2) -> Or(reduce_formula f1, reduce_formula f2)
  | Binop (And,f1,f2) -> And(reduce_formula f1, reduce_formula f2)
  | Binop (_,_,_) -> BadOp 1
  | Not f1 -> Not (reduce_formula f1)
  | Atom x -> reduce_atom x
  | _ -> BadOp 0

let rec simp_iter1 = function
  | Iff (f, True) -> simp_iter1 f
  | Iff (True, f) -> simp_iter1 f
  | Iff (f, False) -> Not (simp_iter1 f)
  | Iff (False, f) -> Not (simp_iter1 f)
  | Iff (f1, Not(f2)) -> if f1 = f2 then False else Iff (simp_iter1 f1, Not(simp_iter1 f2))
  | Iff (Not(f1), f2) -> if f1 = f2 then False else Iff (Not(simp_iter1 f1), simp_iter1 f2)
  | Iff (f1, f2) -> if f1 = f2 then True else Iff (simp_iter1 f1, simp_iter1 f2)
  | Imp (True, f) -> simp_iter1 f
  | Imp (f, True) -> True
  | Imp (False, f) -> True
  | Imp (f, False) -> Not (simp_iter1 f)
  | Imp (f1, Not(f2)) -> if f1 = f2 then False else Not(simp_iter1 f1)
  | Imp (Not(f1), f2) -> if f1 = f2 then False else simp_iter1 f1
  | Imp (f1, f2) -> if f1 = f2 then True else Imp (simp_iter1 f1, simp_iter1 f2)
  | And (f, True) -> simp_iter1 f
  | And (True, f) -> simp_iter1 f
  | And (f, False) -> False
  | And (False, f) -> False
  | And (f1, Not(f2)) -> if f1 = f2 then False else And (simp_iter1 f1, Not(simp_iter1 f2))
  | And (Not(f1), f2) -> if f1 = f2 then False else And (Not(simp_iter1 f1), simp_iter1 f2)
  | And (f1, f2) -> if f1 = f2 then simp_iter1 f1 else And (simp_iter1 f1, simp_iter1 f2)
  | Or (True, f) -> True
  | Or (f, True) -> True
  | Or (False, f) -> simp_iter1 f
  | Or (f, False) -> simp_iter1 f
  | Or (f1, Not(f2)) -> if f1 = f2 then True else Or (simp_iter1 f1, Not(simp_iter1 f2))
  | Or (Not(f1), f2) -> if f1 = f2 then True else Or (Not(simp_iter1 f1), simp_iter1 f2)
  | Or (f1, f2) -> if f1 = f2 then simp_iter1 f1 else Or (simp_iter1 f1, simp_iter1 f2)
  | Not (True) -> False
  | Not (False) -> True
  | Not (f) -> Not (simp_iter1 f)
  | x -> x (* all remaining cases map to themselves *)

let rec simp_iter2 = function
  | Iff (f, True) -> simp_iter2 f
  | Iff (True, f) -> simp_iter2 f
  | Iff (f, False) -> Not (simp_iter2 f)
  | Iff (False, f) -> Not (simp_iter2 f)
  | Iff (f1, f2) ->
    (* create list of equations that are iffed together *)
    let rec iflist = function
      | Iff (f1, f2) -> (iflist f1) @ (iflist f2)
      | x -> [x]
    in
    let iffs = iflist (Iff (f1, f2)) in
    (* create associative list of counts of formulae
       using syntactic equality *)
    let rec compute_counts iffs acc =
      match iffs with
      | i::is ->
        let count =
          match List.Assoc.find acc i with
            | None -> 0
            | Some x -> x
        in compute_counts is (List.Assoc.add acc i (count + 1))
      | [] -> acc
    in
    let counts = compute_counts iffs [] in
    (* reassemble tree of iffed formulae according to
       frequency of their occurrence, and recurse on the
       generated tree *)
    let rec reassemble counts =
      match counts with
      | [] -> failwith "something went wrong"
      | [(c, n)] -> if n mod 2 = 0 then True else simp_iter2 c
      | (c, n)::cs -> if n mod 2 = 0 then reassemble cs else Iff (reassemble cs, simp_iter2 c)
    in reassemble counts
  | Imp (True, f) -> simp_iter2 f
  | Imp (f, True) -> True
  | Imp (False, f) -> True
  | Imp (f, False) -> Not (simp_iter2 f)
  | Imp (f1, Not(f2)) -> if f1 = f2 then False else Not(simp_iter2 f1)
  | Imp (Not(f1), f2) -> if f1 = f2 then False else simp_iter2 f1
  | Imp (f1, f2) -> if f1 = f2 then True else Imp (simp_iter2 f1, simp_iter2 f2)
  | And (f, True) -> simp_iter2 f
  | And (True, f) -> simp_iter2 f
  | And (f, False) -> False
  | And (False, f) -> False
  | And (f1, Not(f2)) -> if f1 = f2 then False else And (simp_iter2 f1, Not(simp_iter2 f2))
  | And (Not(f1), f2) -> if f1 = f2 then False else And (Not(simp_iter2 f1), simp_iter2 f2)
  | And (f1, f2) -> if f1 = f2 then simp_iter2 f1 else And (simp_iter2 f1, simp_iter2 f2)
  | Or (True, f) -> True
  | Or (f, True) -> True
  | Or (False, f) -> simp_iter2 f
  | Or (f, False) -> simp_iter2 f
  | Or (f1, Not(f2)) -> if f1 = f2 then True else Or (simp_iter2 f1, Not(simp_iter2 f2))
  | Or (Not(f1), f2) -> if f1 = f2 then True else Or (Not(simp_iter2 f1), simp_iter2 f2)
  | Or (f1, f2) -> if f1 = f2 then simp_iter2 f1 else Or (simp_iter2 f1, simp_iter2 f2)
  | Not (True) -> False
  | Not (False) -> True
  | Not (f) -> Not (simp_iter2 f)
  | x -> x (* all remaining cases map to themselves *)

let simplify iffs f =
  let rec aux f n =
    (* "SIMPLIFYING ("^(string_of_int n)^"): "^(pretty_string f) |> print_endline; *)
    let f' = (if iffs then simp_iter2 else simp_iter1) f in
    if f = f' then f' else aux f' (n+1)
  in aux f 0


(*** HELPERS ***)

let negate f = Not f
