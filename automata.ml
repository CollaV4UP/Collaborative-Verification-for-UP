(*根据var_list 和 fun_list 得到所有的转移语句  用Set保存*)
open State
(*根据变量名和函数名  得到的所有可能转移*)
module InstrSet = Set.Make(
  struct
    type t = Execution.instr
    let compare = Stdlib.compare
  end)

(*StateSet中compare函数的辅助函数*)
let compare (v1,v2) (v3,v4) =
      let first = compare_var v1 v3 in
      if first = 0 then compare_var v2 v4
      else first
			
let compare_tri (v1,v2,v3) (v4,v5,v6) =
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
			
(*存储所有state的 Set 尝试定义compare方法提高查找效率  *)

let compare_state state1 state2 = 
	
	  let {eq=eq1; dq=dq1; fun_set=fun_set1; _;} = state1 in
		let {eq=eq2; dq=dq2; fun_set=fun_set2;_ ;} = state2 in
    let result = ref 0 in
	  let eq1 = PairSet.elements eq1 in
		let dq1 = PairSet.elements dq1 in
		let fun_set1 = TripleSet.elements fun_set1 in
		let eq2 = PairSet.elements eq2 in
		let dq2 = PairSet.elements dq2 in
		let fun_set2 = TripleSet.elements fun_set2 in
    if (List.length eq1 = List.length eq2)
		 
		  then begin
           List.iter2 (fun v1 v2 -> 
              if  (!result = 0) && not (compare v1 v2 = 0) 
							    then result := (compare v1 v2)  
									else ()    ) eq1 eq2 										
					 ;
					 if (!result = 0)
					
					   then begin
							if (List.length dq1 = List.length dq2)
						         then  begin
											     List.iter2 (fun v1 v2 -> 
				                   if (!result = 0) && not(compare v1 v2 = 0) 
												     then result := (compare v1 v2)  
														 else ()   ) dq1 dq2  
													 ;
														if (!result = 0)
														then begin
															    if (List.length fun_set1 = List.length fun_set2)
																	  then begin
																			    List.iter2 (fun v1 v2 -> 
				                                   if  (!result=0) && not (compare_tri v1 v2 = 0 )
												                   then result := compare_tri v1 v2  
																					 else ()  ) fun_set1 fun_set2    
																				 end																											
																		else result := Stdlib.compare (List.length fun_set1) (List.length fun_set2)
														      end
														else ()
														
													end	
										 else  result := Stdlib.compare (List.length dq1) (List.length dq2)
									 end
					   else ()
					end
		else result := Stdlib.compare (List.length eq1) (List.length eq2)
		;			
		!result
										
(*存储所有state的set*)
module StateSet = Set.Make(
  struct
    type t = int*State.state           
    let compare (num1,state1) (num2,state2)
		              = compare_state state1 state2
  end)       
	
																																		                                                                  
(*存储所有的转移表达式  状态标签*转移指令（list或者单个存储似乎都可）*到达状态标签   *)
module TranSet = Set.Make(
  struct
    type t = int * Execution.instr * int
    let compare (q0,instr1,q1) (q2,instr2,q3) =  
			let first = (Stdlib.compare q0 q2) in
			  if first = 0 then 
					let second = Execution.compare_instr instr1 instr2  in
			       if second = 0	then  (Stdlib.compare q1 q3) 
						 else second
				else 	first			  
  end)


module CoSet = Set.Make (
  struct
    type t = Execution.instr * int
    let compare (instr1,q1) (instr2,q2) = let first = Stdlib.compare instr1 instr2	in
		                                           if first = 0 then  Stdlib.compare q1 q2
																							 else first
  end)

(*存储所有转移表达式的map key: int代表状态  value: (CoSet)代表从键值状态出发的转移*)
module TranMap = Map.Make(
	struct
    type t = int 
    let compare = Stdlib.compare
	end)
type tranMap = CoSet.t TranMap.t

(*辅助作用 *)
module NumSet = Set.Make(
  struct
    type t = int
    let compare = Stdlib.compare
  end)
	
let compare_pair (v1, v2) (v3, v4) = let first = Stdlib.compare  v1 v3 in
		                                 if first = 0 then Stdlib.compare  v2 v4
																		 else first

(*自动机求交时  寻找重复出现的片段时*)
module StatePairSet = Set.Make(
  struct
    type t =  int*int
    let compare  = compare_pair
  end)

	
type automata = {start:int; receive:NumSet.t; tran:tranMap }

  
(*************************************** 得到输入程序的所有指令 ******************************************************)
let rec get_instr regex = 
	let instr_set = InstrSet.empty in
		match regex with 
	| Execution.Concat (regex1, regex2) -> InstrSet.union  (get_instr regex1)  (get_instr regex2)
	| Execution.Union  (regex1, regex2) -> InstrSet.union  (get_instr regex1)  (get_instr regex2)
	| Execution.Star regex -> get_instr regex
	| Execution.Base regex -> InstrSet.add regex instr_set


(*************************************** 输出TranSet ******************************************************)
let tran_visualize tran = 
	let tran_string = TranSet.fold (fun (num1,instr,num2) tran_string -> 
			   "("^(Core.Int.to_string num1)^","^(Execution.string_of_instr instr)^","^(Core.Int.to_string num2)^")"^tran_string  ) tran "" in
	Printf.printf "%s\n"  tran_string


(*************************************** 输出TranMap ******************************************************)
let tranMap_visualize tran = 
	TranMap.iter (fun q0 coset -> 
		             CoSet.iter (fun (instr,q1)  ->
									   let tran_string = "("^(Core.Int.to_string q0)^","^(Execution.string_of_instr instr)^","^(Core.Int.to_string q1)^")" in
										 Printf.printf "%s\n"  tran_string
										   )coset
		           ) tran

					
(*************************************** 输出TranMap的转移数量 *************************************************)					
let comp_tran_num tran = 
		TranMap.fold (fun q0 coset num -> 
		                num + (CoSet.cardinal coset)
		           ) tran	0	  
							
(*************************************** TranSet转为TranMap ******************************************************)							
							
let tranSet_to_tranMap tranSet = 
	 let state_set = TranSet.fold (fun (q0,instr,q1) state_set ->
			                               let state_set = NumSet.add q0 state_set in
																		  NumSet.add q1 state_set   ) tranSet NumSet.empty 	in
																			
	 NumSet.fold (fun q  tranMap -> let coSet = TranSet.fold (fun (q0, instr, q1) coSet ->
		                                                 if q0=q then CoSet.add (instr,q1)  coSet
																										         else coSet    ) tranSet  CoSet.empty  in
															 TranMap.add q coSet tranMap   
												       ) state_set TranMap.empty		
						
(*************************************** TranMap转为TranSet ******************************************************)														
		let tranMap_to_tranSet tranMap  =
				TranMap.fold ( fun q0 coset tranSet ->
					               CoSet.fold (fun (instr,q1) tranSet -> 
													            TranSet.add (q0,instr,q1) tranSet    ) coset tranSet    )  tranMap  TranSet.empty																
																									   
(*
(*************************************** 生成大自动机 *************************************************************)
(*递归生成所有的状态以及转移   *)	

    let rec generate_state state_set  set_temp automata_tr instr_set num num_than_one = 
	
    	let  set_temp_f = 
    		StateSet.fold (fun (state_key,st) set_temp1 -> 
					
					 let coset = ref (CoSet.empty) in
           let result = InstrSet.fold (fun instr set_temp2 ->
    				   	let next_state = State.refresh_state st instr in
    							begin
                   if not (State.is_conflict next_state) then
										  
										 let state_find = StateSet.find_opt (-2,next_state) !state_set in
										 let exist_key = match state_find with
                											| None -> (-1)
                											| Some (key,state) ->  key  in 
    									begin
    									     if (exist_key = -1) then
    												begin																						
    			 								    num := !num + 1 ; 
															state_set := StateSet.add (!num,next_state) !state_set;
															coset := CoSet.add (instr, !num) !coset;    										 
    												  StateSet.add (!num,next_state) set_temp2		
    												end
    					             else 
														begin
														num_than_one := NumSet.add exist_key !num_than_one;
														coset := CoSet.add (instr, exist_key) !coset;
    												set_temp2
														end 
    									end
          				  else 
    									set_temp2
    						 end	
    		    ) instr_set  set_temp1   in
				
				    automata_tr := TranMap.add state_key !coset !automata_tr;
				    result    
				
				)set_temp   StateSet.empty in
				
					
				let state_set_1 = StateSet.cardinal set_temp_f in
				let state_set_2 = StateSet.cardinal !state_set in
     		Printf.printf "%d***"  state_set_1;
				Printf.printf "%d\n"  state_set_2;
				flush stdout; 
    	  if (StateSet.is_empty set_temp_f) then  
					   begin
					   Printf.printf "num_than_one:%d\n" (NumSet.cardinal !num_than_one);
						 let receive = TranMap.fold (fun q0 coset receive -> NumSet.add q0 receive ) !automata_tr NumSet.empty in
					   let big_automata = {start = 0; receive; tran = !automata_tr} in
						 (big_automata,!state_set)
						 end
    		else generate_state state_set  set_temp_f automata_tr instr_set num num_than_one
		
	

(* input :: var_list（List:State.var）: 所有变量的集合   fun_list(List:State.func):所有函数名的集合 instr_set: 可能的指令集和 *)
(* output:: automata_tr(Set:int * string * int):大自动机的所有转移  state_env(Map:int -> State.state):大自动机的所有状态的三元组集合  *)

let init_bigAutomata var_list fun_list instr_set = 	
		
	flush stdout; 
	
	let num = ref 0 in
	let automata_tr = ref (TranMap.empty) in
	let start_state = State.init var_list fun_list in
	let state_set = ref (StateSet.add (0,start_state) StateSet.empty) in
	let num_than_one = ref (NumSet.empty) in
	(generate_state state_set !state_set automata_tr instr_set num num_than_one)
*)
		
	(*************************************** coherent&&correct大自动机 *************************************************************)
(*	
	
	(*递归生成所有的状态以及转移   *)	

    let rec generate_cc_state state_set  set_temp automata_tr instr_set num = 
	
    	let  set_temp_f = 
    		StateSet.fold (fun (state_key,st) set_temp1 -> 
					
					 let coset = ref (CoSet.empty) in
           let result = InstrSet.fold (fun instr set_temp2 ->
						    let v_mem = ref 0 in
	              let v_ear = ref 0 in
								
								let next_state = ref st in
								begin
						     match instr with
		                 | Execution.AssignFromLocToLoc (x,f,y) ->  		
											      begin	   
                            if (Coherence.check_memorize !next_state (x,f,y) ) then  v_mem := 1 else v_mem := !v_mem
                               ;
													  next_state	:= Coherence.refresh_state_item !next_state instr
														end
										 | Execution.AssumeLocEq (x,y) -> 
											      begin
                            next_state := Coherence.refresh_state_item !next_state instr;
                            if (Coherence.check_early_assume !next_state (x,y) ) then v_ear := 1 else v_ear := !v_ear	
														end	
										 |_ ->  next_state := Coherence.refresh_state_item !next_state instr;
										end		
										;																
    				    let next_state = !next_state in
							
    							begin
                   if not (State.is_conflict next_state)&& (!v_mem=0)&&(!v_ear=0) then
										  
										 let state_find = StateSet.find_opt (-2,next_state) !state_set in
										 let exist_key = match state_find with
                											| None -> (-1)
                											| Some (key,state) ->  key  in 
    									begin
    									     if (exist_key = -1) then
    												begin																						
    			 								    num := !num + 1 ; 
															state_set := StateSet.add (!num,next_state) !state_set;
															coset := CoSet.add (instr, !num) !coset;    										 
    												  StateSet.add (!num,next_state) set_temp2		
    												end
    					             else 
														begin
														coset := CoSet.add (instr, exist_key) !coset;
    												set_temp2
														end 
    									end
          				  else 
    									set_temp2
    						 end	
    		    ) instr_set  set_temp1   in
				
				    automata_tr := TranMap.add state_key !coset !automata_tr;
				    result    
				
				)set_temp   StateSet.empty in
				
    	  if (StateSet.is_empty set_temp_f) then  
					   let receive = TranMap.fold (fun q0 coset receive -> NumSet.add q0 receive ) !automata_tr NumSet.empty in
					   let big_automata = {start = 0; receive ; tran = !automata_tr} in
						 (big_automata,!state_set)
    		else generate_cc_state state_set  set_temp_f automata_tr instr_set num
		
	

(* input :: var_list（List:State.var）: 所有变量的集合   fun_list(List:State.func):所有函数名的集合 instr_set: 可能的指令集和 *)
(* output:: automata_tr(Set:int * string * int):大自动机的所有转移  state_env(Map:int -> State.state):大自动机的所有状态的三元组集合  *)

let init_cc_bigAutomata var_list fun_list instr_set = 	
		
	flush stdout; 
	
	let num = ref 0 in
	let automata_tr = ref (TranMap.empty) in
	let start_state = State.init var_list fun_list in
	let state_set = ref (StateSet.add (0,start_state) StateSet.empty) in
	(generate_cc_state state_set  !state_set automata_tr instr_set num)

	*)	
	
	(************************************************** 程序自动机 ***********************************************************)
	
  (*concat*)
let concat_set  (t1, s1 ,e1 )  (t2, s2, e2) = 
	  let t = if s1=e1
 				       then  begin let t = TranSet.fold (fun (num1,instr,num2) t ->
																	 let num_s = if num1=s2
																	                then s1
																									else num1  in
																	TranSet.add (num_s,instr,num2) t  ) t2 TranSet.empty  in
														TranSet.union t t1 
										end 
																	
	             else begin  
								       let t = TranSet.fold (fun (num1,instr,num2) t ->
																	 let num_e = if num2=e1
																	                then s2
																									else num2  in
																	TranSet.add (num1,instr,num_e) t  ) t1 TranSet.empty  in
																	TranSet.union t t2 
												end    in
				(t,s1,e2)														
	
		(*union*)	
  let union_set (t1, s1 ,e1 )  (t2, s2, e2)  = 		  
    let t =  TranSet.fold (fun (num1,instr,num2) t ->
			                             let num_s = if num1=s2 
																	                 then s1
																									 else num1 in
																	 let num_e = if num2=e2
																	                then e1
																									else num2  in
																	TranSet.add (num_s,instr,num_e) t  ) t2 t1 in
		    	
	  (t, s1, e1)
		
		(*star*)
  let star_set (t0, s0, e0) = 
		let t = TranSet.fold (fun (num1,instr,num2) t ->
			                        if num2 = e0
															   then  TranSet.add (num1,instr,s0) t 															      
																 else  TranSet.add (num1,instr,num2) t ) t0 TranSet.empty in
		(t,s0,s0)
	  
		
(*返回值 t s e 分别表示  转移本身   该转移集合的开头    该转移集合的结尾 ;;   循环 的开头和结尾  q instr q  表示，其中 q 为该循环的 入口状态*)
let rec get_pro_automata rgx num = 
		 match rgx with 
      	| Execution.Concat (regex1, regex2) -> concat_set (get_pro_automata regex1 num) (get_pro_automata regex2 num)
      	| Execution.Union  (regex1, regex2) -> union_set (get_pro_automata regex1 num) (get_pro_automata regex2 num)
      	| Execution.Star regex -> star_set (get_pro_automata regex num)
      	| Execution.Base regex -> num := !num + 2;
	       (TranSet.add (!num-1,regex,!num-2) TranSet.empty,(!num-1),(!num-2) )

(*处理为标准形式*)
let  pro_automata rgx = 
	   let num = ref 0 in
     let (pro_automata,start_num,end_num) = get_pro_automata rgx num in
		 let pro_automata = tranSet_to_tranMap pro_automata in
		 {start = start_num ; receive = (NumSet.add end_num NumSet.empty) ; tran = pro_automata} 






