
(* NNF conversion - eliminates implication/equivalence
  and pushes negation to literals *)
(* standard conversion *)
val nnf1 : Problem_ast.formula -> Problem_ast.formula
(* polarity dependent conversion *)
val nnf2 : Problem_ast.formula -> Problem_ast.formula

(* converts formula in NNF to CNF via distributing over And *)
val cnf : Problem_ast.formula -> Problem_ast.formula

(* complete function from problem to cnf formula *)
val to_cnf : int -> Problem_ast.formula -> Problem_ast.formula

(* for converting formulas to sets of clauses *)
val clausify : Problem_ast.formula -> Clause.t
val problemify : Problem_ast.formula -> Clause_set.t

type result = Theorem of string | CounterSatisfiable

val get_proof : result -> string option
val res_str : result -> string

(* resolve two clauses together generating a set of
   clauses (clauses may resolve in more than one way) *)
val resolve : Clause.t -> Clause.t -> Log.t

(* removes tautologies *)
val process : Clause_set.t -> Clause_set.t

(* given clause algorithm - the main part of the
   resolution procedure *)
val given_clause : (Clause_set.t -> Clause.t option) -> Clause_set.t -> Clause_set.t -> Log.t -> bool -> bool -> bool -> result
