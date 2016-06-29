open Core.Std
open Clause

include Set.Make(Clause)

let choose_unitpref cls =
  match find cls ~f:(fun cl -> Clause.is_unit cl) with
  | Some x -> Some x
  (* fall back on arbitrary choose function *)
  | None -> choose cls

let pure_literals cls =
  let combined = fold ~init:Clause.empty ~f:(fun acc x -> Clause.union acc x) cls in
  match Clause.split combined with
  | (pos,neg) ->
    let negneg = Clause.neg_all neg in
    let union_ = Clause.union pos negneg in
    let inter_ = Clause.inter pos negneg in
    Clause.diff union_ inter_

let to_string cls = cls
  |> to_list 
  |> List.map ~f:Clause.to_string
  |> String.concat ~sep:" "
