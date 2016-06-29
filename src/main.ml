open Core.Std
open Problem_ast
open Tptp_ast
open Solve

let rec sort_problem pl goal assum iffs =
  match pl with
  | (Fof_anno af)::ps -> (
    let f =
      match af.af_formula with
      | Formula g -> g
      | Sequent (_,_) -> failwith "ERRSEQ"
    in
    match af.af_role with
    (* assumptions & the rest *)
    | R_axiom | R_hypothesis | R_definition | R_assumption | R_lemma | R_theorem | R_corollary
    | R_plain | R_fi_domain | R_fi_functors | R_fi_predicates | R_type | R_unknown ->
      sort_problem ps goal ((f |> reduce_formula |> (simplify iffs))::assum) iffs
    (* goal formulas *)
    | R_conjecture ->
      sort_problem ps ((f |> reduce_formula |> Problem_ast.negate |> (simplify iffs))::goal) assum iffs
    | R_negated_conjecture ->
      sort_problem ps ((f |> reduce_formula |> (simplify iffs))::goal) assum iffs
  )
  (* for pattern matching warning *)
  | _::ps -> sort_problem ps goal assum iffs
  (* return the problem when done *)
  | [] -> (goal, assum)

let run up init cnf pl iffs sub filename debug =
  (* Obtain Tptp_ast.tptp_input list of filename *)
  let tptp = Tptp.File.read filename in
  (* separate goals from assumptions *)
  match sort_problem tptp [] [] iffs with
  | (goal, assum) ->
    (* if any formula False then end *)
    if List.exists ~f:(fun x -> x = False) (goal @ assum) then Theorem "Problem simplified to true" else
    (* remove True formulae *)
    let not_true = (function True -> false | _ -> true) in
    let goal_ = List.filter ~f:not_true goal in
    let assum_ = List.filter ~f:not_true assum in
    (* if problem now empty we stop - everything was true *)
    if List.length (goal_ @ assum_) = 0 then CounterSatisfiable else
    (* run resolution on what remains *)
    let map = fun x -> x |> (Solve.to_cnf cnf) |> Solve.problemify in
    (* Clause_set.to_string (List.map ~f:map goal_  |> Clause_set.union_list |> (Solve.process false)) |> print_endline; *)
    let goal  = List.map ~f:map goal_  |> Clause_set.union_list |> Solve.process in
    let assum = List.map ~f:map assum_ |> Clause_set.union_list |> Solve.process in
    (* "GOAL: "^(Clause_set.to_string goal) |> print_endline; *)
    (* "ASSUMPTIONS: "^(Clause_set.to_string assum) |> print_endline; *)
    let combined = Clause_set.union goal assum in
    (* Pick a choosing function (arbitrary or unit preference) *)
    let choose = if up then Clause_set.choose_unitpref else Clause_set.choose in
    (* Create the initial log for proof tracing (contains only starting clauses) *)
    let il = List.map (Clause_set.to_list combined) ~f:(fun x -> (x, None)) in
    (* Here we choose starting conditions for the given clause algorithm. *)
    let unused =
      if init = 1 then combined
      else if init = 2 then goal
      else (* if init = 3 then *) Clause_set.filter ~f:Clause.is_all_neg combined
    in
    let used =
      if init = 1 then Clause_set.empty
      else if init = 2 then assum
      else (* if init = 3 then *) Clause_set.diff combined (Clause_set.filter ~f:Clause.is_all_neg combined)
    in Solve.given_clause choose unused used il sub pl debug

let print_result v result =
  if v then (
    "RESULT: " ^ Solve.res_str result |> print_endline;
    let proof = match Solve.get_proof result with Some proof -> "PROOF:\n" ^ proof | None -> "" in
    proof |> print_endline;
  ) else Solve.res_str result |> print_endline

let spec =
  let open Command.Spec in
  empty
  +> flag "-v" no_arg ~doc:"verbose mode"
  +> flag "-debug" no_arg ~doc:"debug mode"
  +> flag "-unit" no_arg ~doc:" run with unit preference"
  +> flag "-init" (optional_with_default 1 int) ~doc:"1: std, 2: sos=goal, 3: sos=allneg"
  +> flag "-cnf" (optional_with_default 1 int) ~doc: "1: naive, 2: polarity dependent"
  +> flag "-pl" no_arg ~doc:" use pure literal deletion"
  +> flag "-iffs" no_arg ~doc:"simplify iffs more"
  +> flag "-sub" no_arg ~doc:"use subsumption"
  +> anon ("file" %: file)

let command =
  Command.basic
    ~summary:"A resolution theorem prover"
    ~readme:(fun () -> "More detailed information")
    spec
    (fun v debug unitpref init cnf pl iffs sub file () ->
      if v then (
        "\n=== INFORMATION ===\n" |> print_endline;
        "PROBLEM: " ^ file |> print_endline;
        "SIMPLIFICATION: " ^ (if iffs then "maximal" else "minimal") |> print_endline;
        "CNF STRATEGY: " ^ (if cnf = 1 then "naive" else "polarity dependent") |> print_endline;
        "SOS STRATEGY: " ^ (if init=1 then "none" else if init=2 then "assumptions" else "all-negative clauses") |> print_endline;
        "SELECTION STRATEGY: " ^ (if unitpref then "unit preference" else "arbitrary") |> print_endline;
        "PURE LITERAL DELETION: " ^ (if pl then "on" else "off") |> print_endline;
        "SUBSUMPTION: " ^ (if sub then "on" else "off") |> print_endline;
        "\n=== PROVING ===\n" |> print_endline;
      );
      let r = run unitpref init cnf pl iffs sub file debug in
      if v then "\n=== RESULT ===\n" |> print_endline;
      print_result v r;
      if v then "" |> print_endline;)

let () =
  Command.run command
