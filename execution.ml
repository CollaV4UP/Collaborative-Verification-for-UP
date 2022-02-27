module StringSet = Set.Make(
  struct
    type t = string
    let compare =Stdlib.compare 
  end)


type execRegex =
  | Concat of execRegex * execRegex
  | Union of execRegex * execRegex
  | Star of execRegex
  | Base of instr

and instr =
  | UpdateLocToData of string * string list * string
  | UpdateLocToLoc of string * string list * string
  | AssignFromLocToData of string * string * string list
  | AssignFromLocToLoc of string * string * string list
  | AssignFromDataToData of string * string * string list
  | AssignFromData of string * string
  | AssignFromLoc of string * string
  | AssumeLocEq of string * string
  | AssumeLocNeq of string * string
  | AssumeDataEq of string * string
  | AssumeDataNeq of string * string
  | Free of string
  | Alloc of string
  | Exception
  | Skip

let neg c =
  match c with
  | Ast.Eq(v1,v2) -> Ast.Neq(v1,v2)
  | Ast.Neq(v1,v2) -> Ast.Eq(v1,v2)

let rec regexOfStmt env stm =
  match stm with

  | Ast.Seq(s1,s2) -> Concat(regexOfStmt env s1, regexOfStmt env s2)

  | Ast.Assert(c) ->
      Base(regexOfCond env (neg c))
		(* Union
      (Concat (Base(regexOfCond env (neg c)), Base(Exception)),
       Concat (Base(regexOfCond env c), Base(Skip)))  *)

  | Ast.Skip -> Base(Skip)

  | Ast.Assume(c) -> Base(regexOfCond env c)

  | Ast.Assign(t1, t2) ->
    (match t1, t2 with

     | Var i1, Var i2 ->
       (match Typechecker.lookup i1 env, Typechecker.lookup i2 env with
        | Data, Data -> Base(AssignFromData(i1, i2))
        | Location, Location -> Base(AssignFromLoc(i1, i2))
        | _ -> failwith "Typechecker is buggy")

     | App (i1, args), Var i2 ->
       (match Typechecker.lookup i1 env, Typechecker.lookup i2 env with
        | LocToLoc, _ -> Base(UpdateLocToLoc(i1, args, i2))
        | LocToData, _ -> Base(UpdateLocToData(i1, args, i2))
        | _ -> failwith "Typechecker is buggy")

     | Var i1, App (i2, args) ->
       (match Typechecker.lookup i1 env, Typechecker.lookup i2 env with
        | _, LocToLoc -> Base(AssignFromLocToLoc(i1, i2, args))
        | _, LocToData -> Base(AssignFromLocToData(i1, i2, args))
        | _, DataToData(arity) -> Base(AssignFromDataToData(i1, i2, args))
        | _ -> failwith "Typechecker is buggy")

     | _, _ -> failwith "Typechecker is buggy")

  | Ast.Free(i) -> Base(Free(i))

  | Ast.Alloc(i) -> Base(Alloc(i))

  | Ast.While(c,s) ->
    Concat
      (Star(Concat (Base(regexOfCond env c), regexOfStmt env s)),
       Base(regexOfCond env @@ neg c))

  | Ast.Ite(c,s1,s2) ->
    Union
      (Concat (Base(regexOfCond env c), regexOfStmt env s1),
       Concat (Base(regexOfCond env @@ neg c), regexOfStmt env s2))

and regexOfCond env c =
  match c with
  | Ast.Eq(i1, i2) ->
    (match Typechecker.lookup i1 env with
     | Data -> AssumeDataEq(i1, i2)
     | Location -> AssumeLocEq(i1, i2)
     | _ -> failwith "Typechecker is buggy")
  | Ast.Neq(i1, i2) ->
    (match Typechecker.lookup i1 env with
     | Data -> AssumeDataNeq(i1, i2)
     | Location -> AssumeLocNeq(i1, i2)
     | _ -> failwith "Typechecker is buggy")

let regexOfProg env (preamble_opt, stm) =
  match preamble_opt with
  | None -> regexOfStmt env stm
  | Some (Ast.Preamble(_, Ast.InitLoc(init_list))) ->
    List.fold_right
      (fun (i1, i2) acc ->
         Concat(Base(AssignFromLoc(i1, i2)), acc))
      init_list (regexOfStmt env stm)
	
(*-----------------------------------------regexToString----------------------------------------------------*)
let string_of_list  string_list =
	let s = List.fold_left (fun s x -> s^x) "" string_list in
		s


let rec string_of_regex execRegex = 	
	match execRegex with 
	| Concat (regex1, regex2) -> (string_of_regex regex1 )^";"^(string_of_regex regex2 )
	| Union  (regex1, regex2) -> "{"^(string_of_regex regex1 )^"+"^(string_of_regex regex2 )^"}"
	| Star regex -> "["^(string_of_regex regex )^"]"^"*"
	| Base regex -> 
		(match regex with
        | UpdateLocToData (x,y,z) -> x^(string_of_list y)^z
        | UpdateLocToLoc (x,y,z) -> x^(string_of_list y)^z
        | AssignFromLocToData (x,y,z) -> x^y^(string_of_list z)
        | AssignFromLocToLoc (x,f,y) -> x^":="^f^"("^(string_of_list y)^")"           (*x:=f(y)*)
        | AssignFromDataToData (x,y,z) -> x^y^(string_of_list z)
        | AssignFromData (x,y) -> x^y
        | AssignFromLoc (x,y) -> x^":="^y                                             (*x:=y*)
        | AssumeLocEq (x,y) -> "assume"^"("^x^"="^y^")"                               (*assume(x=y)*)
        | AssumeLocNeq (x,y) -> "assume"^"("^x^"!="^y^")"                             (*assume(x!=y)*)
        | AssumeDataEq (x,y) -> x^y
        | AssumeDataNeq (x,y) -> x^y
        | Free x -> x
        | Alloc x -> x
        | Exception -> "Execption"
        | Skip -> "Skip"
     )
		
(*----------------------------------------- instrToString ----------------------------------------------------*)

let string_of_instr instr = 
	
		match instr with
      
        | AssignFromLocToLoc (x,f,y) -> x^":="^f^"("^(string_of_list y)^")"           (*x:=f(y)*)
        | AssignFromLoc (x,y) -> x^":="^y                                             (*x:=y*)
        | AssumeLocEq (x,y) -> "assume"^"("^x^"="^y^")"                                (*assume(x=y)*)
        | AssumeLocNeq (x,y) -> "assume"^"("^x^"!="^y^")"                             (*assume(x!=y)*)
				| Skip -> "eplision"
				| _ -> Printf.printf "%s" "unsupport instr"; assert false

let compare_instr instr1 instr2 = 
	match (instr1,instr2) with
	| (AssignFromLocToLoc (x1,f1,y1),AssignFromLocToLoc (x2,f2,y2)) -> if x1=x2 && f1=f2 && y1=y2 then 0 else (-1)
	| (AssignFromLoc (x1,y1),AssignFromLoc (x2,y2)) -> if x1=x2 && y1=y2 then 0 else (-1)
	| (AssumeLocEq (x1,y1),AssumeLocEq (x2,y2)) -> if x1=x2 && y1=y2 then 0 else (-1)
	| (AssumeLocNeq (x1,y1),AssumeLocNeq (x2,y2)) -> if x1=x2 && y1=y2 then 0 else (-1)
	| _ -> (-1)

(*-----------------------------------------------  取出一条指令中的变量--------------------------------------------------*)
let get_var_instr instr =
	  match instr with
        | AssignFromLocToLoc (x,f,y) -> (x,string_of_list y)          
        | AssignFromLoc (x,y) -> (x,y)                                         
        | AssumeLocEq (x,y) -> (x,y)                             
        | AssumeLocNeq (x,y) ->  (x,y)                          
				| _ -> Printf.printf "%s" "unsupport instr"; assert false

let get_fun_instr  instr = 
	  match instr with
        | AssignFromLocToLoc (x,f,y) -> (x,f,string_of_list y)                                
				| _ -> Printf.printf "%s" "unsupport instr"; assert false

(*
let rec get_re_var_auxi  env stm re_var = 
	  
	  match stm with
		 | Ast.Seq(s1,s2) -> get_re_var_auxi  env s1 re_var; get_re_var_auxi  env s2 re_var
     | Ast.Assert(c) ->
			  begin
			    match c with
            | Ast.Eq(i1, i2) -> re_var := StringSet.add  i1 !re_var; re_var := StringSet.add  i2 !re_var
            | Ast.Neq(i1, i2) -> re_var := StringSet.add  i1 !re_var; re_var := StringSet.add  i2 !re_var
				end
		 | Ast.While(c,s) -> get_re_var_auxi  env s re_var
     | Ast.Ite(c,s1,s2) -> get_re_var_auxi  env s1 re_var
		 | _ -> ()
		 
		
let get_re_var  env (preamble_opt, stm) = 
	 let re_var = ref StringSet.empty in
	 get_re_var_auxi  env stm re_var;
	 !re_var
*)


