open Core.Std

type resolution = Clause.t * (Clause.t * Clause.t) option

type t = resolution list

let dedup log =
  let rec aux used acc = function
    | (c,x)::ls -> if Clause_set.mem used c then aux used acc ls else aux (Clause_set.add used c) ((c,x)::acc) ls
    | [] -> acc
  in aux Clause_set.empty [] log

let clean log =
  let rec aux log used acc =
    match log with
    | (c, r)::ls ->
      if Clause_set.mem used c then match r with
        | Some(c1,c2) -> aux ls (Clause_set.add (Clause_set.add used c1) c2) ((c, Some(c1,c2))::acc)
        | None -> aux ls used ((c, None)::acc)
      else aux ls used acc
    | [] -> acc
  in aux log (Clause_set.singleton Clause.empty) []

let to_string log =
  let res_string = function
    | (c, Some(c1,c2)) -> (Clause.to_string c) ^ " <- " ^ (Clause.to_string c1) ^ ", " ^ (Clause.to_string c2)
    | (c, None) -> (Clause.to_string c) ^ " <-"
  in
  List.fold (clean (dedup (List.rev log))) ~f:(fun acc x -> acc ^ (res_string x) ^ "\n") ~init:""
