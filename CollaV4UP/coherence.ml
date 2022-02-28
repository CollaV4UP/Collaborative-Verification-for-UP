open State
(* ------------------------------------------------------------------- coherent判断相关 --------------------------------------------------------------------------- *)

module StringSet = Set.Make(
  struct
    type t = string
    let compare =Stdlib.compare 
  end)

(*检查当前状态是否违反memorizing  true表示违反*)
let check_memorize st (x,f,y) =
	 let f = func_of_string f in
	 let y = var_of_string(string_of_list y) in
	
   let item_set = ItemSet.filter (fun (f0,a,b)  ->  f0=f && a=y && b=true ) st.item in
	 let fun_set = TripleSet.filter (fun (f0,a,b) -> f0=f && a=y && b=Undef ) st.fun_set in

	 if ( not (ItemSet.is_empty (item_set) )  && not (TripleSet.is_empty (fun_set) ) )
	   then true
		 else false

(*递归检查一个项的超项是否被丢弃*)
let rec check_early_assume_auxi   st x flag num = 
	 if !num > 500
	    then ()
			else 
      	  let candidate_set = TripleSet.filter (fun (f,a,b) -> (compare_var a x)=0 ) st.fun_set in
      	(*	State.visualize st; *)
      	  let item_set = ItemSet.filter (fun (f,a,b) ->  (compare_var a x)=0 ) st.item in
          TripleSet.iter (fun (f0,a0,b0) ->
                         ItemSet.iter (fun (f1,a1,b1)  ->
      										     if f0=f1  
      												    then if ( b0=Undef && b1=true ) then
      															  flag := true
      														else if (b0 != Undef && b1=true &&  ( compare_var a0 (var_of_dep b0) ) != 0 )
      														     then  begin  (* Printf.printf "%s\n"  (string_of_dep_var b0);*) num := !num+1;  check_early_assume_auxi  st (var_of_dep b0) flag num  end 
      																 else ()
      												 else ()   )   item_set   ) candidate_set
												

(*检查当前状态是否违反early-assume  true表示违反*)	
let check_early_assume   st (x,y) =		
	 let flag_x = ref false in
   let flag_y = ref false in 
	 let x = var_of_string x in
	 let y = var_of_string y in
	 let num = ref 0 in
	 check_early_assume_auxi   st x flag_x  num ;
	 let num = ref 0 in
	 check_early_assume_auxi   st y flag_y  num ; 
	 (!flag_x  || !flag_y)  
	 
(*更新  item *)
let refresh_state_item st instr = 
	match instr with
  | Execution.AssignFromLocToLoc (x,f,y) -> fun_assign_refresh st (var_of_string x, func_of_string f,var_of_string(string_of_list y) )  true             (*x:=f(y)*)
  | Execution.AssignFromLoc (x,y) -> assign_refresh st (var_of_string x,var_of_string y)  true                                                           (*x:=y*)
  | Execution.AssumeLocEq (x,y) -> assume_eq_refresh  st  (var_of_string x,var_of_string y)  true                                                        (*assume(x=y)*)
  | Execution.AssumeLocNeq (x,y) -> assume_deq_refresh st (var_of_string x,var_of_string y)                                                              (*assume(x!=y)*)
	| _ -> Printf.printf "%s" "unsupport instr"; assert false


(*------------------------------------------------------------ 由一条路径得到其对应的状态序列 ----------------------------------------------------------------------------*)	

(*由路径得到其变量、函数列表*)
let  get_var_fun  execution =
	   let var_list = ref StringSet.empty in
     let fun_list = ref StringSet.empty in	
		 Array.iter (fun instr ->
			              	match instr with
                            | Execution.AssignFromLocToLoc (x,f,y) ->   var_list := StringSet.add x !var_list;
															                                          var_list := StringSet.add (Execution.string_of_list y) !var_list;
																																				fun_list := StringSet.add f !fun_list
																																				
                            | Execution.AssignFromLoc (x,y) ->          var_list := StringSet.add x !var_list;
															                                          var_list := StringSet.add y !var_list
																																				
                            | Execution.AssumeLocEq (x,y) ->            var_list := StringSet.add x !var_list;
															                                          var_list := StringSet.add y !var_list
																																				
                            | Execution.AssumeLocNeq (x,y) ->           var_list := StringSet.add x !var_list;
															                                          var_list := StringSet.add y !var_list
                          	| _ -> Printf.printf "%s" "unsupport instr"; assert false   ) execution   ;
		 ( (StringSet.elements  !var_list) ,(StringSet.elements  !fun_list) )
		 
(*修改插入assume(t=k)的位置  改为在assume语句之前  t和k最后被赋值的位置  *)
(*------------------------------------------ 将assume语句提前  0:表示将assume语句提前，原来的assume不删除    1:删掉原来的assume语句 -----------------------------*)
let assume_ahead    execution state_array assume_instr location  =
		let insert_location = ref (-1) in
		let execution_ahead = ref [||] in
		let (x,y) = Execution.get_var_instr assume_instr in
		
	(*	Array.iteri (fun i instr ->
			                 let (a,b) = Execution.get_var_instr instr  in
											 if (!insert_location < location) && ( String.equal a x || String.equal a y || String.equal b x || String.equal b y ) 
											    then  insert_location := i
													else () ) execution;  *)
		(*寻找最后被赋值的地方*)											
		Array.iteri (fun i instr ->
											 match instr with
											  |  Execution.AssumeLocEq (a,b) ->  ()
												|  Execution.AssumeLocNeq (a,b) ->  ()
												|  _  ->   let (a,b) = Execution.get_var_instr instr  in
													         if  (!insert_location < location) && ( String.equal a x || String.equal a y ) 
              											   then  insert_location := i
              												 else ()      ) execution;
																			
		(*若最后被赋值的地方为 （-1）  寻找最先出现的位置 *)							
		let flag1 =	ref false in													
		let flag2 = ref false in													
		if (!insert_location = (-1) )
		   then   Array.iteri (fun i instr ->
				         match instr with
									  |  Execution.AssumeLocEq (a,b) ->  ()
										|  Execution.AssumeLocNeq (a,b) ->  ()
										|  _  ->   let (a,b) = Execution.get_var_instr instr  in
											         if (!insert_location < location)
											          then  begin
																	       if (String.equal b x)  &&  not !flag1 
																				   then  begin
																						      flag1 := true;
																									if !flag2
																									   then insert_location := i
																								 end
																								;
																				 if ( String.equal b y) &&  not !flag2
																				   then  begin
																						      flag2 := true;
																									if !flag1 
																									   then insert_location := i
																								 end
																	    end
													       else ()   ) execution;								
													
		
	  Array.iteri (fun i instr ->			                  
												if (i=(!insert_location) )
                           then 
														 begin
														 execution_ahead := Array.append !execution_ahead [|instr|];													
													   execution_ahead := Array.append !execution_ahead [|assume_instr|]
														 end
													 else 													 
														 if i = location
														    then ()
																else execution_ahead := Array.append !execution_ahead [|instr|]                   																											
											 ) execution
			                 ;
		(!execution_ahead, !insert_location)

(*判断路径是否coherent  具体思路：遇到x=f(y)判断memorizing  遇到assume(x==y)判断是否违反early-assume   暂时支持只有一个early_assume的情况*)
let is_coherence  execution state_array = 
	let v_mem = ref 0 in
	let v_ear = ref 0 in
	Array.iteri (fun i instr ->		
    		match instr with
    		| Execution.AssignFromLocToLoc (x,f,y) ->  			   
    			   if (check_memorize  state_array.(i) (x,f,y) ) 
    				     then  begin (* Printf.printf "%s" x ; *) v_mem := 1 end
    						 else  v_mem := !v_mem				 
    				
    		| Execution.AssumeLocEq (x,y) -> 
    			   if (check_early_assume  state_array.(i) (x,y) ) 
    				    then  v_ear := 1
    						else  v_ear := !v_ear				 
    				
    		| _ -> ()			
		
       ) execution
		;
	 			
	(*	Array.iteri (fun i instr ->
			 	if i>0 then  Printf.printf "-------------------------- %s ---------------------------\n" ( Execution.string_of_instr execution.(i-1) ) 
					     else  Printf.printf "---------------------------------------------------------\n" ;  
	      State.visualize state_array.(i)               ) state_array;     *)
				
   
	 (!v_mem,!v_ear)
			

(*-------------------------------------------------------------------  路径可达性判断  ---------------------------------------------------------------------------------*)
						
(*对于非coherent的路径，添加中间变量使其coherent*)
let make_coherent execution var_list = 
	let num = ref 0 in
	let execution_coh = ref [||] in
	let var_list = ref var_list in
	Array.iter (fun instr -> match instr with 
                 	| Execution.AssignFromLocToLoc (x,f,y) -> let insert = Execution.AssignFromLoc ("#"^(Core.Int.to_string !num),x) in 									                                           
																														 var_list := List.append  !var_list  ["#"^(Core.Int.to_string !num )];
																														 num := !num+1;
																														 execution_coh := Array.append !execution_coh [|insert|];
									                                           execution_coh := Array.append !execution_coh [|instr|]
																													   
																														
									| _ -> execution_coh := Array.append !execution_coh [|instr|]
									                              ) execution  
                  ;
	(!execution_coh,!var_list)

(*由一条路径得到相应的状态序列*)
let get_state_array  execution =						
	    let (var_list,fun_list) = get_var_fun execution in
			
		  let state_temp = ref (State.init var_list fun_list) in
	  	let state_ary =  ref [|!state_temp|] in
	    
      Array.iter (fun  instr ->				 
                 state_temp := refresh_state_item   !state_temp instr;
					       state_ary := Array.append !state_ary  [|!state_temp|]    ) execution
			;
		  !state_ary   	
	

(*对路径是否可达的判断   flag  0:路径可行  1:中间不可行   2:路径不可行   *)
let is_feasible  execution var_list fun_list =
	
	  let state_array = get_state_array  execution  in
   (* let is_end = ref true in  *)
	  let flag = ref 0 in
		
		let loca = ref (-1) in
		Array.iteri ( fun i state ->									               
			                 if (is_conflict state) 
															 then begin 																								     
																			 if ( i = Array.length state_array )
																			    then  begin
																						      if !flag = 0
																									   then flag := 2;
																						    end
																					else  if !loca = (-1)
																					         then begin loca := i; flag := 1; 	end
																									 else ()																									
																			 end 																									   
																  else ()
												 ) state_array;
												
	  (* Array.iter (fun state -> Printf.printf "-----------------------------------------------\n"; State.visualize  state  ) state_array;  *)
		if (!flag = 1 || !flag = 2 )
		   then  begin  (* Printf.printf "flag:%d\n" !flag; Printf.printf "%d\n" (!loca-1); Printf.printf "length:%d\n" (Array.length state_array) ; *) !flag  end
			 else 							          									 
             let (execution,var_list) = make_coherent  execution var_list  in
						
					  (* Printf.printf "%s\n "  "******************* 使其 coherent **********************"; 
					   Array.iter (fun  instr ->  Printf.printf "%s\n " (Execution.string_of_instr instr) 	) execution;  *)
						 
             let state = ref (init var_list fun_list) in
      	     Array.iteri ( fun i instr -> state := refresh_state !state instr;	
															 	
                     (*  Printf.printf "------------  %s ----------------\n" (Execution.string_of_instr instr);
											 State.visualize !state; 	*)																																																																											                
                       if (is_conflict !state) 
											    then begin 
														    flag := 3;																						   
															(*	 Printf.printf "----------------------------location:%d-------------------\n" i;
																 flush stdout;  *)
															(*	 State.visualize  !state;  	*)																							
															 end      ) execution;														 

    		!flag

(*-------------------------------------------------------------------  将memorizing的路径变成coherent的  ---------------------------------------------------------------------------------*)

let delete_item  execution location =
	  let execution_new = ref [||] in
	  Array.iteri (fun i instr ->
			               if i = location
										    then ()
												else execution_new := Array.append !execution_new [|instr|]  )  execution ;
	  !execution_new

let change_name  execution location =
	  let execution_new = ref [||] in
	  Array.iteri (fun i instr ->
			               if i = location
										    then begin
													     let (x,y) = Execution.get_var_instr instr in
															 let instr = Execution.AssignFromLoc("@"^(Core.Int.to_string i),y) in
															 execution_new := Array.append !execution_new [|instr|] 
													   end 
												else execution_new := Array.append !execution_new [|instr|]  )  execution ;
	  !execution_new

let rec make_mem_coherent_auxi execution = 	  	  
		let flag = ref false in
		Array.iteri (fun i instr ->						
									   let (x,y) = Execution.get_var_instr instr in
										            if String.sub x 0 1 = "#"  && not !flag
																   then
																		  let execution_temp = delete_item   !execution i in
																      let state_array_temp = get_state_array  execution_temp in
															      	let (v_mem,v_ear) = is_coherence   execution_temp  state_array_temp in
																      if v_mem=0 && v_ear=0
																         then begin 
																					      execution := execution_temp;
																								make_mem_coherent_auxi execution
																							end
																	       else  execution := change_name !execution i;
																				       make_mem_coherent_auxi execution
																			 ;
																			flag := true
																	 else ()
													 
										 ) !execution
	

let make_mem_coherent execution = 	
	  let (execution_temp,_) = make_coherent  execution [] in
		let execution = ref execution_temp in
    make_mem_coherent_auxi  execution;
	(*	Printf.printf "-----------------------lalala--\n";
		Array.iter (fun instr -> Printf.printf "%s\n" (Execution.string_of_instr instr)  ) !execution ;  *)
		!execution


