
(* resolution type *)
type resolution = Clause.t * (Clause.t * Clause.t) option

(* log type - stores list of resolutions *)
type t = resolution list

(* get string of proof from log *)
val to_string : t -> string
