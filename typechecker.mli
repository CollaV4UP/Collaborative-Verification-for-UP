type env

type t =
  | Data
  | Location
  | LocToLoc
  | LocToData
  | DataToData of int

val print_env : env -> unit
val typecheck : Ast.prog -> env
val names :
  Ast.preamble option -> env ->
  string list * string list * string list  * string list * string list
val lookup : string -> env -> t