type var = Var of string                               (*变量*)
type func = Func of string                             (*函数名*)
type dep_var =  Depvar of var | Undef                  (*因变量*)

let string_of_var x = match x with Var s -> s
let var_of_string s = Var s

let string_of_func f = match f with Func s -> s
let func_of_string s = Func s

let string_of_dep_var v = match v with Depvar s -> string_of_var s | Undef -> "Undef"   
let dep_var_of_string s = match s with "Undef" -> Undef | _ -> Depvar (var_of_string s)

let var_of_dep x = match x with  Undef -> Printf.printf "unspport dep_var"; assert false  | Depvar s  -> s

let compare_var x y =
  Stdlib.compare (string_of_var x) (string_of_var y)

let compare_func x y =
  Stdlib.compare (string_of_func x) (string_of_func y)

let compare_dep_var x y =
	 Stdlib.compare (string_of_dep_var x) (string_of_dep_var y)

let string_of_list  string_list =
	let s = List.fold_left (fun s x -> s^x) "" string_list in
		s

module VarSet = Set.Make(
  struct
    type t = var
    let compare (v1) (v2) =
      let first = compare_var v1 v2 in
      first
  end)
	
module PairSet = Set.Make(
  struct
    type t = var * var
    let compare (v1,v2) (v3,v4) =
      let first = compare_var v1 v3 in
      if first = 0 then compare_var v2 v4
      else first
  end)
	
module TripleSet = Set.Make(
  struct
    type t = func * var * dep_var
    let compare (v1,v2,v3) (v4,v5,v6) =
      let first = compare_func v1 v4 in
      if first = 0 then let second = compare_var v2 v5 in
			                   if second = 0 
												     then  match (v3,v6) with
														| (Undef,Undef) -> 0
														| ((Depvar s1),(Depvar s2)) -> compare_var s1 s2
														| (Undef, Depvar s) -> compare_var (Var "0") s
														| (Depvar s, Undef) -> compare_var s (Var "0")
												                    
											   else second
      else first
  end)
	
	
module ItemSet = Set.Make(
  struct
    type t = func * var * bool
    let compare (v1,v2,v3) (v4,v5,v6) =
      let first = compare_func v1 v4 in
      if first = 0 then  let second = compare_var v2 v5		in	  
			                    if second = 0  then match (v3,v6) with
													                     |(true,false) -> 1
																							 |(false,true) -> -1
																							 | _ -> 0    
													else second             
      else first
  end)
	
type state = {eq : PairSet.t;
              dq : PairSet.t;
              fun_set : TripleSet.t;
							item : ItemSet.t }

(*----------------------------------状态是否相等的比较---------------------------------*)

(* Equality of eq *)
let equal_eq eq1 eq2 = PairSet.equal eq1 eq2
let equal_dq dq1 dq2 = PairSet.equal dq1 dq2
let equal_fun_set fun_set1 fun_set2 = TripleSet.equal fun_set1 fun_set2


(* Equality of states  三元组形式的状态判等 *)
let equal st1 st2 =
  let {eq=eq1;dq=dq1;fun_set=fun_set1;_;} = st1 in
  let {eq=eq2;dq=dq2;fun_set=fun_set2;_;} = st2 in
  (equal_eq eq1 eq2) &&
  (equal_dq dq1 dq2) &&
  (equal_fun_set fun_set1 fun_set2)

(* 等价关系和不等价关系是否冲突 *)
let is_conflict st = 
	if (PairSet.is_empty st.eq) && (PairSet.is_empty st.dq) 
	  then	false
		else   let inter = PairSet.inter st.eq st.dq in
		      (* PairSet.iter(fun (x,y) ->  Printf.printf "(%s,"  (string_of_var x);
					                            Printf.printf "%s)\n"  (string_of_var y) ) inter;
																			Printf.printf "--------------------------------------\n"; *)
	         not (PairSet.is_empty inter)


(* --------------------------- Visualizing states ------------------------------------ *)

let print_var d x = (string_of_var x)
let print_dep_var x = match x with Depvar s -> string_of_var s | Undef -> "Undef" 

let print_pair f (x,y) =
  "("^(f x)^", "^(f y)^")"

let print_triple (x,y,z) =
	"("^(string_of_func x)^","^(string_of_var y)^","^(print_dep_var z)^")"

let visualize_eq st = 
	  let eq = st.eq in
  "{ "^
  (PairSet.fold
     (fun x acc ->
        (print_pair (print_var 0) x) ^", "^ acc) eq "")
				 ^" }"
				
let visualize_deq st =
  let deq = st.dq in
  "{ "^
  (PairSet.fold
     (fun x acc ->
        (print_pair (print_var 0) x) ^", "^ acc) deq "")
				 ^" }"
				
let visualize_funs st =  
	let func = st.fun_set in
	 "{ "^
	 (TripleSet.fold
	      (fun x acc ->
					(print_triple x)^","^acc) func "")
					 ^" }"

let visualize_item st = 
	let item = st.item in
	  "{ "^
	 (ItemSet.fold
	      (fun (f,a,bool) acc ->
					"("^(string_of_func f)^","^(string_of_var a)^","^(Core.Bool.to_string bool)^")"^acc) item "")
					 ^" }"

let visualize st =
  print_string @@ "EqClasses: "^visualize_eq st^"\n";
  print_string @@ "Disequalities: "^visualize_deq st^"\n";
  print_string @@ "Funs: \n"^visualize_funs st^"\n";
	print_string @@ "Items: \n"^visualize_item st^"\n" 
(* --------------------------------------- init -------------------------------------- *)

let init_func var_list fun_list =
	let func_temp = ref TripleSet.empty in
	  List.iter (fun f -> 
			(List.iter (fun x -> 
				 func_temp := TripleSet.add (func_of_string f, var_of_string x, Undef) !func_temp ) var_list) ) fun_list;
		!func_temp

let init_item var_list fun_list = 
	let item_temp = ref ItemSet.empty in
	  List.iter (fun f -> 
			(List.iter (fun x -> 
				 item_temp := ItemSet.add (func_of_string f, var_of_string x, false) !item_temp ) var_list) ) fun_list;
		!item_temp


let  init var_list fun_list = 
	let eq = PairSet.empty in
	let dq = PairSet.empty in
	let fun_set = init_func var_list fun_list in
	let item = init_item var_list fun_list in
	{eq;dq;fun_set;item}

(* --------------------------------------- refresh -------------------------------------- *)
 

(*x是被修改的变量，(a,b) 中是否有被修改影响的变量 *)         
let is_add (a,b) x =	
	if  not ( (compare_var a x ) = 0 || (compare_var b x) = 0)
	  then true
		else false

let is_add_fun (a,b) x = 
	 match b with
	| Undef -> false
	| Depvar s -> is_add (a,s) x

(*获取一个变量的等价类元素都有哪些*)      
let get_eqclass eq x = 
	 PairSet.fold (fun (a,b) set -> if( (compare_var a x ) = 0 ) then VarSet.add b set  else set
		  ) eq VarSet.empty 
  
	
(*获取一个变量的不等价类元素都有哪些*) 
let get_dqclass dq x = 
		PairSet.fold (fun (a,b) set -> if( (compare_var a x ) = 0 ) then VarSet.add b set  else set
		  ) dq VarSet.empty 
  
(*在等价关系 eq 下，将（a,b）的等价关系的二元组加入到 set_old中，得到新的*)	
let add_eq_pair eq set_old (x,y) flag = 
	
	let right_eq = get_eqclass eq y in
	let right_eq = VarSet.add y right_eq in
			 
	if flag then 
      let left_eq = get_eqclass eq x in
			let left_eq = VarSet.add x left_eq in
      
          VarSet.fold (fun a set_old->    
                 (VarSet.fold( fun b set_old  -> if  (compare_var a b) = 0
								then set_old
							  else  let set = PairSet.add (a,b) set_old in 
								       PairSet.add (b,a) set 	   )  ) right_eq  set_old  )    left_eq  set_old 
	 else 
			  	VarSet.fold( fun b set_old  -> if(compare_var x b = 0)
							 then set_old
							 else let set = PairSet.add (x,b) set_old in 
											PairSet.add (b,x) set    ) right_eq  set_old 
															           


let add_dq_pair dq set_old (a,b) flag = 
	
    if flag then 
        let left_dq = get_dqclass dq a in
        let right_dq = get_dqclass dq b in						 
        let set_old = VarSet.fold (fun x set_old->    
                                          if (compare_var b x = 0) 
																					   then set_old
																						 else let set = PairSet.add (b,x) set_old in PairSet.add (x,b) set    )  left_dq  set_old   in
											
				VarSet.fold( fun y set_old  -> if(compare_var a y = 0)
					               then set_old
				                 else let set = PairSet.add (a,y) set_old in PairSet.add (y,a) set    ) right_dq  set_old 						
															
		else 
           let right_dq = get_dqclass dq b in
				  	    VarSet.fold( fun y set_old  -> if(compare_var a y = 0)
									then set_old
								  else let set = PairSet.add (a,y) set_old in PairSet.add (y,a) set    ) right_dq  set_old 



(*x := y 赋值语句的三元组更新*)
let assign_refresh st (x,y) refresh_item = 
	  (*更新eq*)
	  let eq = PairSet.fold (fun (a,b) tmp_eq ->
			if ( is_add (a,b) x ) then  PairSet.add (a,b) tmp_eq else tmp_eq ) st.eq  PairSet.empty  in
  	let eq = (add_eq_pair st.eq eq (x,y) false ) in
		
		(*更新dq*)
		let dq = PairSet.fold (fun (a,b) dq ->
			if ( is_add (a,b) x ) then  PairSet.add (a,b) dq else dq ) st.dq  PairSet.empty  in
		let dq = ( add_dq_pair st.dq dq (x,y) false ) in
				
		
		(*更新fun*)
		let fun_set = TripleSet.fold ( fun (f,a,b) fun_set ->  
			 if( is_add_fun (a,b) x ) then 
				TripleSet.add (f,a,b) fun_set 
			 else 				
				match b with 
				| Undef -> TripleSet.add (f,a,Undef) fun_set
				| Depvar s ->  if (compare_var s x) = 0 then let set_temp = get_eqclass st.eq x in 
				                              if VarSet.is_empty set_temp then TripleSet.add (f,a,Undef) fun_set  
											                else TripleSet.add (f,a, Depvar (VarSet.min_elt set_temp) ) fun_set
											 else TripleSet.add (f,a,Undef) fun_set
				                          ) st.fun_set TripleSet.empty  in	
		
		let fun_temp = TripleSet.fold ( fun (f,a,b) fun_temp -> if  (compare_var a y = 0) then
  		                                                        match b with 
  																														| Undef -> fun_temp
  																														| _ ->  TripleSet.add (f,a,b) fun_temp
  		                                                     
																													 else fun_temp		                                       
		                                      )fun_set TripleSet.empty    in																				
																					
																					
		let fun_set =TripleSet.fold (fun (f,a,b) fun_set -> let fun_set = TripleSet.add (f,x,b) fun_set  in
		                                                  TripleSet.remove (f,x,Undef) fun_set  ) fun_temp fun_set  in		
		
		(*更新item*)
		   let item =	if refresh_item 
		                    then  
													ItemSet.fold (fun (f,a,bool) item ->													
				                      if  (compare_var a x) = 0 then  
																   if (ItemSet.mem (f,y,true) st.item)
																	     then  ItemSet.add (f,a,true) item
																			 else ItemSet.add (f,a,false) item
										           else ItemSet.add (f,a,bool) item  ) st.item  ItemSet.empty 
			                  
			          else  st.item  in
		{eq;dq;fun_set;item}

(*x := f(y) 赋值语句的三元组更新*)	
let  fun_assign_refresh st (x,f0,y) refresh_item = 
	let (isDefind, def_var) = TripleSet.fold ( fun (f,a,b) pair -> if ( (compare_func f f0) = 0 && (compare_var a y) = 0  ) 
	                                         then match b with
																				       	| Undef -> pair
																								| Depvar s -> (true, s)
																					 else pair) st.fun_set (false,var_of_string "")   in

    if isDefind && (compare_var def_var x = 0 )
		   then st
			 else        (*更新eq*)
                	 let eq= PairSet.fold (fun (a,b) eq ->
                			if ( is_add (a,b) x ) then  PairSet.add (a,b) eq else eq ) st.eq  PairSet.empty  in				
                (*	 Printf.printf "**%s+"   (	(string_of_var x)^":="^(string_of_func  f0)^"("^(string_of_var y)^")"  );	
									 Printf.printf "%s\n\n"  (string_of_var def_var);  *)
											
                	 let eq =  if (isDefind) then		
                		     add_eq_pair st.eq eq (x, def_var ) false 
                	     else eq  in                		
											
                		(*更新dq*)
                		let dq = PairSet.fold (fun (a,b) dq ->
                			if ( is_add (a,b) x ) then  
                				PairSet.add (a,b) dq 
                				else dq 
                				) st.dq  PairSet.empty  in				
                		let dq = if isDefind then ( add_dq_pair st.dq dq (x,  def_var ) false ) else dq  in
                		
                		
                   (*更新fun_set*)
                		let fun_set = 			
                			if isDefind  
											    then  begin
                				         let fun_set = TripleSet.fold ( fun (f,a,b) fun_set ->  
                          				             if( is_add_fun (a,b) x ) 
                          				    	       then  TripleSet.add (f,a,b) fun_set
                          				    	       else  match b with 
                          								            | Undef -> TripleSet.add (f,a,Undef) fun_set
                          								            | Depvar s ->  if compare_var a y = 0 && compare_var  s x = 0 && (compare_func f f0)=0
                          														                   then  TripleSet.add (f,a,b) fun_set
                          																							 else  if (compare_var s x = 0) && not (compare_var a s = 0)
                                      														                then let set_temp = get_eqclass st.eq x in 
                                      								                                 if VarSet.is_empty set_temp 
                          																														      then TripleSet.add (f,a,Undef) fun_set  
                                      															                        else TripleSet.add (f,a, Depvar (VarSet.min_elt set_temp) ) fun_set
                                      															                   else TripleSet.add (f,a,Undef) fun_set    ) st.fun_set TripleSet.empty   in
                										
                                    					 (*加入 x 对应于 dep_var 的函数关系*)			
                                    					 let fun_temp = TripleSet.fold ( fun (f,a,b) fun_temp -> 
                                    						                                       if   a=def_var  
                                    	                                                       then match b with 
                                    																												   | Undef -> fun_temp
                                    																													 | _ ->  TripleSet.add (f,a,b) fun_temp 
                                    																												 else fun_temp		                                       
                                    	                                         )fun_set TripleSet.empty    in					 																														
                                    																				
                                               TripleSet.fold (fun (f,a,b) fun_set -> let fun_set = TripleSet.add (f,x,b) fun_set  in
                                    	                                                  TripleSet.remove (f,x,Undef) fun_set  ) fun_temp fun_set		
																	end  
                       else 			
                				  begin
                					 let set_x = 	get_eqclass st.eq x in					 
                				   let fun_set = TripleSet.fold ( fun (f,a,b) fun_set ->  
                				             if( is_add_fun (a,b) x ) 
                				    	       then  TripleSet.add (f,a,b) fun_set
                				    	       else  match b with 
                								            | Undef -> TripleSet.add (f,a,Undef) fun_set
                								            | Depvar s ->  if (compare_var s x = 0) && not (compare_var a s = 0)
                														                  then    if VarSet.is_empty set_x then TripleSet.add (f,a,Undef) fun_set  
                															                        else TripleSet.add (f,a, Depvar (VarSet.min_elt set_x) ) fun_set
                															                else TripleSet.add (f,a,Undef) fun_set    ) st.fun_set TripleSet.empty   in
                							
                					let set_y =  get_eqclass st.eq y in
                					let set_y = VarSet.add y set_y in																																		
                					TripleSet.fold (fun  (f,a,b) fun_set ->
                						                    if  (compare_func f f0)=0  &&  VarSet.mem a set_y && ( not (compare_var a x =0))
                																   then  begin 
                																		       let fun_set = TripleSet.remove (f,a,b) fun_set in
                																		       TripleSet.add (f,a,Depvar x) fun_set
                																			   end	
                																	 else  fun_set
                																  ) fun_set fun_set;
                				end                                                in																																																											    
                							
                			(*更新item*)
                	   let item =	if refresh_item 
                		               then 	
                										let y_eqal = get_eqclass st.eq y in	 
                										let y_eqal = VarSet.add y y_eqal in
                										let item = ItemSet.fold (fun (f,a,bool) item ->
                											                    if VarSet.mem a y_eqal &&  f = f0
                																					   then begin 
                																							      let item = ItemSet.remove (f,a,bool) item in
                																										ItemSet.add (f,a,true) item																										 
                																						      end
                																						 else ItemSet.add (f,a,bool) item
                																						      ) st.item  st.item    in
                										              
                									  let item = ItemSet.fold (fun (f,a,bool) item ->
                											                    if a=x &&  TripleSet.mem (f,a,Undef) fun_set
                																					   then begin 
                																							      let item = ItemSet.remove (f,a,bool) item in
                																										ItemSet.add (f,a,false) item																										 
                																						      end
                																						 else ItemSet.add (f,a,bool) item
                																						      ) item  item    in			
                										let x_eq = get_eqclass eq x in	
                										ItemSet.fold (fun (f,a,bool) item -> 
                											                 if VarSet.mem a x_eq && bool = true
                																			    then begin
                																						     let item = ItemSet.remove (f,x,bool) item in
                																								 ItemSet.add (f,x,true) item 
                																						   end 
                																					else  item   ) 	item item
                			                      
                			           else st.item  in
   									(*		Printf.printf "%s\n" ( "{ "^
                                      (PairSet.fold
                                         (fun x acc ->
                                            (print_pair (print_var 0) x) ^", "^ acc) eq "")
                                    				 ^" }"	) ;			*)
											
											
                		{eq;dq;fun_set;item}
            

(*assume(x == y) 赋值语句的三元组更新*)
(*辅助更新eq*)
let rec eq_refresh fun_set eq = 
   let eq_new = TripleSet.fold(fun (f,a,b) eq ->  
			                       ( TripleSet.fold (fun (g,c,d)  eq ->
															    if(compare_func f g = 0) 
																	then  let set = get_eqclass eq a  in
																	      if  not ( b = Undef || d = Undef )  && (VarSet.mem c set || (compare_var a c )=0 )  &&  not ( (compare_dep_var b d )=0 ) 
																				  then   
																						    let left = var_of_string (string_of_dep_var b) in
																								let right = var_of_string (string_of_dep_var d) in
																								add_eq_pair eq eq (left,right) true
																				  else   eq
																	else 	
																		eq
																 ) fun_set  eq )   ) fun_set  eq  in
	if eq=eq_new then eq
	else eq_refresh fun_set eq_new
	

let assume_eq_refresh st (x,y) refresh_item = 	
	  
		(*更新eq*)
		let eq = ( add_eq_pair st.eq st.eq (x,y) true ) in		
		let eq = eq_refresh st.fun_set eq  in
		
		(*更新dq*)
		let dq = st.dq in
		let dq = ( add_dq_pair st.dq dq (x,y) true ) in
		
		(*更新fun   只关心 x 和 y 的函数关系就行  和 x 等价的变量  若有函数关系 则都有*)
		let fun_x_temp = TripleSet.fold ( fun (f,a,b) fun_temp -> if  (compare_var a x = 0)
		                                                       then TripleSet.add (f,a,b) fun_temp
																													 else fun_temp		                                       
		                                      )st.fun_set TripleSet.empty    in		
																					
		let fun_y_temp = TripleSet.fold ( fun (f,a,b) fun_temp -> if  (compare_var a y = 0)
		                                                       then TripleSet.add (f,a,b) fun_temp
																													 else fun_temp		                                       
		                                      )st.fun_set TripleSet.empty    in	
																					
	  let fun_set = TripleSet.fold (  fun (f, a, b) fun_set ->
		                              TripleSet.fold ( fun (g,c,d) fun_set ->
																		         if (compare_func f g = 0)
																						 then 
																							match (b,d) with
																					    	| (Undef,Depvar s) -> 
																									            let eq_set = get_eqclass st.eq a in
																															let eq_set = VarSet.add a eq_set in																														
																															VarSet.fold (fun a fun_set ->
																																   let fun_set = TripleSet.add (f,a,Depvar s) fun_set in
																																	 TripleSet.remove (f,a,Undef) fun_set      ) eq_set fun_set
																								                       
																					    	| (Depvar s,Undef) -> 
																									            let eq_set = get_eqclass st.eq c in
																															let eq_set = VarSet.add c eq_set in
																															VarSet.fold (fun a fun_set ->
																																    let fun_set = TripleSet.add (f,a,Depvar s) fun_set in
																																		TripleSet.remove (f,a,Undef) fun_set  ) eq_set fun_set
																																																							
																					    	| _ -> fun_set  
																							else fun_set
																							) fun_y_temp  fun_set      ) fun_x_temp  st.fun_set    in
																							
		(*更新item*)
	   let item =	if refresh_item 
		                    then 
			                    let left_set = ItemSet.filter (fun (f,a,bool) -> (compare_var a x = 0) ) st.item in
													let right_set = ItemSet.filter (fun (f,a,bool) -> (compare_var a y = 0) ) st.item in
													
													let eq_class = get_eqclass eq x in
													let eq_class = VarSet.add x eq_class in
													let eq_class = VarSet.add y eq_class in
													
													ItemSet.fold  (fun (f,a,bool) item -> 
														    if  (VarSet.mem a eq_class) &&  ( ( ItemSet.mem (f,x,true) left_set )  ||  ( ItemSet.mem (f,y,true) right_set )   ) 
																    then ItemSet.add (f,a,true) item
																		else ItemSet.add (f,a,bool) item  ) st.item ItemSet.empty 
													
			          else  st.item  in
											
		{eq;dq;fun_set;item}


(*assume(x != y) 赋值语句的三元组更新*)	 
let assume_deq_refresh st (x,y) = 
	
	 (*更新eq*)
   let eq = st.eq in
	
	 (*更新dq*)
 	 let dq = ( add_eq_pair eq st.dq (x,y) true)  in
		
	 (*更新fun*)
   let fun_set = st.fun_set in
	 {eq;dq;fun_set;item =  st.item}
	
			
(*根据 Instr 更新 state 的函数*)
(* input :: st(State.state):读入指令之前的状态   instr(Execution.instr):读入的指令  *)
(* output::   *)
let refresh_state st instr = 
	match instr with
  | Execution.AssignFromLocToLoc (x,f,y) -> fun_assign_refresh st (var_of_string x, func_of_string f,var_of_string(string_of_list y) )  false            (*x:=f(y)*)
  | Execution.AssignFromLoc (x,y) -> assign_refresh st (var_of_string x,var_of_string y)   false                                                         (*x:=y*)
  | Execution.AssumeLocEq (x,y) -> assume_eq_refresh  st  (var_of_string x,var_of_string y)  false                                                       (*assume(x=y)*)
  | Execution.AssumeLocNeq (x,y) -> assume_deq_refresh st (var_of_string x,var_of_string y)                                                              (*assume(x!=y)*)
	| _ -> Printf.printf "%s" "unsupport instr"; assert false

(*------------------------------------------------------------------------------------------------------------------------------*)



