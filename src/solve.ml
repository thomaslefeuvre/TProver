open Core.Std

open Problem_ast

open Literal
open Clause
open Clause_set


(*** NNF CONVERSION ***)

let rec lift1 = function
  | Iff (f1, f2) -> And(lift1 (Imp(f1, f2)), lift1 (Imp(f2, f1)))
  | Imp (f1, f2) -> Or(Not(lift1 f1), lift1 f2)
  | And (f1, f2) -> And(lift1 f1, lift1 f2)
  | Or (f1, f2) -> Or(lift1 f1, lift1 f2)
  | Not f -> Not(lift1 f)
  | x -> x

let rec lift2 f p =
  match f, p with
  | Iff (f1, f2), 1 -> lift2 (And(Imp(f1, f2), Imp(f2, f1))) 1
  (* Below `_` is matched but it will only catch -1 (done to prevent compiler warning) *)
  | Iff (f1, f2), _ -> Or(And(lift2 f1 (-1), lift2 f2 (-1)), And(Not(lift2 f1 1), Not(lift2 f2 1)))
  | Imp (f1, f2), p -> Or(Not(lift2 f1 (-p)), lift2 f2 p)
  | And (f1, f2), p -> And (lift2 f1 p, lift2 f2 p)
  | Or  (f1, f2), p -> Or (lift2 f1 p, lift2 f2 p)
  | Not f, p -> Not (lift2 f (-p))
  | x, _ -> x

let rec push_negation f =
  match f with
  | And (f1, f2) -> And(push_negation f1, push_negation f2)
  | Or  (f1, f2) -> Or(push_negation f1, push_negation f2)
  | Not (And(f1, f2)) -> Or(push_negation (Not f1), push_negation (Not f2))
  | Not (Or(f1, f2)) -> And(push_negation (Not f1), push_negation (Not f2))
  | Not (Not f1) -> push_negation f1
  | x -> x

let nnf1 f = lift1 f |> push_negation

let nnf2 f = lift2 f 1 |> push_negation


(*** CNF CONVERSION ***)

let rec cnf f =
  let rec dist = function
    | (f1,And(f2,f3)) -> And(dist (f1,f2), dist (f1,f3))
    | (And(f1,f2),f3) -> And(dist (f1,f3), dist (f2,f3))
    | (f1,f2) -> Or(f1,f2)
  in
  match f with
  | And(f1,f2) -> And(cnf f1, cnf f2)
  | Or(f1,f2) -> dist (cnf f1, cnf f2)
  | Not(Atom x) -> Not(Atom x)
  | Atom x -> Atom x
  | x -> failwith "not nnf"

let to_cnf n f = f |> (if Pervasives.(=) n 1 then nnf1 else nnf2) |> cnf


(*** CNF AST CONVERSION ***)

let rec clausify = function
  | Or(f1,f2)   -> Clause.union (clausify f1) (clausify f2)
  | Not(Atom x) -> Clause.singleton (Neg, x)
  | Atom x      -> Clause.singleton (Pos, x)
  | _ -> failwith "not a nnf disjunction"

let rec problemify = function
  | And(f1,f2)  -> Clause_set.union (problemify f1) (problemify f2)
  | Or(f1,f2)   -> Clause_set.singleton (Clause.union (clausify f1) (clausify f2))
  | Not(Atom x) -> Clause_set.singleton (Clause.singleton (Neg, x))
  | Atom x      -> Clause_set.singleton (Clause.singleton (Pos, x))
  | _ -> failwith "not a cnf problem"


(*** RESOLUTION ***)

type result = Theorem of string | CounterSatisfiable

let get_proof = function Theorem t -> Some t | _ -> None

let res_str = function
  | Theorem t -> "Theorem"
  | CounterSatisfiable -> "CounterSatisfiable"

let resolve cl1 cl2 =
  let neg_cl2 = neg_all cl2 in
  (* intersection is the set of symbols that can be resolved *)
  let rs = Clause.inter cl1 neg_cl2 in
  let rec aux rs acc =
    match Clause.choose rs with
    | None     -> acc (* nothing left to resolve, return acc *)
    | Some res ->
      let new_cl = Clause.union (Clause.remove cl1 res) (Clause.remove cl2 (neg res)) in
      let resolution = (new_cl, Some(cl1, cl2)) in
      aux (Clause.remove rs res) (resolution::acc)
  in aux rs []

let rec replace cl cls =
  match Clause_set.to_list cls with
  | [] -> Clause_set.singleton cl
  | c::cls -> if Clause.subset cl c
    then (
      Clause_set.of_list (cl::cls)
    )
    else Clause_set.of_list (c::(Clause_set.to_list (replace cl (Clause_set.of_list cls))))

let incorporate gcl cl unused =
  if Clause.tautology cl || Clause_set.exists ~f:(fun c -> Clause.subset c cl) (Clause_set.add unused gcl)
  then unused else (
    replace cl unused
  )

let process cls = Clause_set.filter ~f:(fun x -> not (Clause.tautology x)) cls

let pure_literal_delete used unused =
  let combined = Clause_set.union used unused in
  let pure_literals = Clause.union (Clause_set.pure_literals combined) (Clause.neg_all (Clause_set.pure_literals combined)) in
  let unused = Clause_set.filter ~f:(fun x -> Clause.inter pure_literals x |> Clause.is_empty) unused in
  let used = Clause_set.filter ~f:(fun x -> Clause.inter pure_literals x |> Clause.is_empty) used in
  (used, unused)

let rec given_clause choose unused used log sub pl debug =
  (* pure literal deletion *)
  let (used, unused) = if pl then pure_literal_delete used unused else (used, unused) in
  if Clause_set.mem unused Clause.empty then Theorem (Log.to_string log) else
  match choose unused with (* pick given clause *)
  | None -> CounterSatisfiable
  | Some gc ->
    let used' = Clause_set.add used gc in
    (* fold function - accumilates list of new resolutions *)
    let ffn =  fun acc x -> acc @ (resolve gc x) in
    (* create the list of resolutions *)
    let resolutions = Clause_set.fold used' ~init:[] ~f:ffn in
    (* extract the set of possible new clauses from `resolutions` *)
    let new_cls = Clause_set.of_list (List.map resolutions ~f:(function (x,_) -> x)) in
    let unused' = if sub then Clause_set.fold ~init:unused ~f:(fun acc x -> incorporate gc x acc) new_cls else Clause_set.union (process new_cls) unused in
    let unused'' = Clause_set.diff unused' used' in (* removing given clause and anything from used *)
    (* DEBUG CODE BEGIN (debug halts so you can proceed step by step) *)
    if debug then (
      (* OUTPUTS: |unused|,|used|,GC,unused,used *)
      let line = input_line stdin in (
        (Clause_set.length unused |> string_of_int) ^ " | "
        ^ (Clause_set.length used |> string_of_int) ^ " | "
        ^ (Clause.to_string gc) ^ " | "
        ^ (Clause_set.to_string unused) ^ " | "
        ^ (Clause_set.to_string used) |> print_endline
      )
    );
    (* DEBUG CODE END *)
    given_clause choose unused'' used' (resolutions @ log) sub pl debug
