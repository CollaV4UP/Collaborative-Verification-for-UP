open Automata
open State
open Execution

module LoopSet = Set.Make(
  struct
    type t = int*int*int
    let compare = Stdlib.compare		
  end)

module Gmap = Map.Make(
	struct 
		type t = string
	  let  compare = Stdlib.compare
	end)
type state_num_map = int Gmap.t

module StringSet = Set.Make(
  struct
    type t = string
    let compare =Stdlib.compare 
  end)

(*------------------------------------------------------------- 泛化得到循环的情况  -----------------------------------------------------------------------*)	
(*泛化得到循环*)
let gen_loop  execution  var_list fun_list instr_set = 
	let num = ref 0 in
  
	let not_end = ref false in
(*获取对应的状态序列*)
  let execution_co = Coherence.make_mem_coherent 	execution in
	let state_ary_temp = Coherence.get_state_array  execution_co in 
	let state_ary0 = ref [|state_ary_temp.(0)|] in
	let num = ref 0 in
		Array.iteri (fun i instr_co ->
			          if  execution.(!num) = instr_co
								    then  begin 
											      state_ary0 := Array.append  !state_ary0 [|state_ary_temp.(i+1)|];
														num := !num + 1
										      end
										else  ()    )  execution_co ;		
										
	let state_ary = ref [||] in			
	let loc = ref (-1) in					
	Array.iteri (fun i state ->
		        if is_conflict state && !loc = (-1)
						   then loc := i
							 else ()
							;
		        let eq = PairSet.fold (fun (x,y) eq ->
									  if String.equal  (String.sub (string_of_var x) 0 1 ) "@"  || String.equal  ( String.sub (string_of_var y) 0 1 ) "@" 
			                  then  eq
				                else  PairSet.add (x,y) eq        ) state.eq PairSet.empty in
								
					  let dq = PairSet.fold (fun (x,y) dq ->
                    if String.equal   (String.sub (string_of_var x) 0 1 ) "@"  || String.equal  ( String.sub (string_of_var y) 0 1 ) "@" 
							           then  dq
								         else  PairSet.add (x,y) dq      ) state.dq  PairSet.empty  in
												
					  let fun_set = TripleSet.fold (fun (f,x,y)  fun_set ->
                  if ( String.equal (String.sub (string_of_dep_var y) 0 1 )  "@" )  &&  not (String.equal (String.sub (string_of_var x) 0 1)  "@" )
										 then  begin 
											       let eq_class = get_eqclass state.eq (var_of_dep y) in
														 let temp = ref (Var "1") in
														 VarSet.iter (fun var_x ->
															                if ( String.equal (String.sub  (string_of_var var_x) 0 1 )  "@" ) 
																							   then  ()
																								 else  temp := var_x ) eq_class;
														 if ( compare_var !temp	(Var "1") = 0  )
														    then 	TripleSet.add  (f,x,Undef) fun_set					
																else  TripleSet.add  (f,x, (Depvar !temp) ) fun_set													       
													 end																		 
										 else  if ( String.equal ( String.sub (string_of_var x)  0 1 )  "@" )
										           then  fun_set
							                 else  TripleSet.add (f,x,y) fun_set  ) state.fun_set  TripleSet.empty  in 
															
						 let state_new = 	{eq;dq;fun_set;item=ItemSet.empty}	in
					   state_ary := Array.append  !state_ary [|state_new|]   ) !state_ary0;			
	
	(* Array.iter (fun state -> visualize state  ) !state_ary; *)
	
	if(!loc < Array.length execution)			
	  then  not_end := true
		;			
	let execution_temp = ref [||] in			
	Array.iteri (fun i instr ->   
		                 if  i < !loc
										     then execution_temp := Array.append !execution_temp [|instr|]
												 else () ) execution;			
  let execution = !execution_temp in															

  (*获取循环出现的语句片段*)
	let same_pair = ref StatePairSet.empty in
  Array.iteri (fun i1 instr1 ->
         Array.iteri (fun i2 instr2 ->
					     if (i2>i1) && ( instr1 = instr2) 
							    then 
										begin
											      if (i2+(i2-i1))<=(Array.length execution)
        										      then  
																		begin
																			 let flag = ref true in
																		
																		   for j = 1 to (i2-i1-1) do
																				 if not (  execution.(i1+j) = execution.(i2+j)   )
																				   then flag := false
																					 else flag := !flag
																		   done
																			 ;
																			 if !flag
																			   then same_pair := StatePairSet.add (i1,i2) !same_pair
																				 else ()   
																		end     													      
        											else ()
										end
									else ()
				          	) execution   )     execution
			;
	(*对应的三元组状态序列,判断对应状态是否相同 *)	
if  not (StatePairSet.is_empty !same_pair )								
		then begin
			
			(*处理三次及以上循环  找到循环最早开始  以及找到最小循环体*)
  	let (a_temp, b_temp) = StatePairSet.min_elt !same_pair in	
  	let a_temp = ref a_temp in
  	let b_temp = ref b_temp in
  	StatePairSet.iter ( fun (a,b) -> if  (!a_temp < a  &&  a < !b_temp) || ( !b_temp < a && a < !b_temp+(!b_temp- !a_temp) ) || ( !a_temp = a && !b_temp != b )  || (!b_temp = a && ( b != !b_temp+(!b_temp- !a_temp) )  ) 
  	                                    then same_pair := StatePairSet.remove (a,b) !same_pair
  																			else if !b_temp <= a
  																			     then begin
  																						    a_temp := a;
  																					      b_temp := b
  																								end
  																					 else ()   ) 	!same_pair	
  																		  ;
		(*	
	 	Printf.printf "%s" "********************** 找到的循环为 *******************************************\n";																
                 StatePairSet.iter (fun (a,b) -> Printf.printf "%d," a; 
                  Printf.printf "%d\n" b ) 			!same_pair   ;     *)

(*
(*得到对应的状态序列*)															
	 let state_ary =  ref [|(State.init var_list fun_list)|] in
	 let state_temp = ref (State.init var_list fun_list) in
   Array.iter (fun  instr ->				 
    state_temp := begin
				 match instr with
              | Execution.AssignFromLocToLoc (x,f,y) -> 
						    fun_assign_refresh !state_temp (var_of_string x, func_of_string f,var_of_string(string_of_list y) )  false                   (*x:=f(y)*)
			
              | Execution.AssignFromLoc (x,y) -> 
				        assign_refresh !state_temp (var_of_string x,var_of_string y)   false 
																																																													       	           (*x:=y*)
              | Execution.AssumeLocEq (x,y) -> 
			          assume_eq_refresh  !state_temp  (var_of_string x,var_of_string y)  false                                                     (*assume(x=y)*)
											
              | Execution.AssumeLocNeq (x,y) -> 
				        assume_deq_refresh !state_temp (var_of_string x,var_of_string y)                                                             (*assume(x!=y)*)
									
  	          | _ -> Printf.printf "%s" "unsupport instr"; assert false end
  		        ;
					    state_ary := Array.append !state_ary  [|!state_temp|]                              ) execution
		          ;
	*)	
		

		
	(*	Array.iteri (fun i st -> Printf.printf "%i\n" i ;
                     State.visualize st  ) !state_ary;  *)
     StatePairSet.iter (fun (a,b) -> 
          let flag = ref true in
							   for j=0 to b-a do
									  if not (State.equal  !state_ary.(a+j)  !state_ary.(b+j) )  
										 then flag := false 
										 else ()
									done  		
						     ;
			if !flag then () else    same_pair := StatePairSet.remove(a,b) !same_pair  ) !same_pair
      ;


(*去掉单条语句的循环   以及处理成   （循环开始位置，单个循环结束位置，所有循环结束位置）形式 *)
			let loop_f = ref LoopSet.empty in
			 begin
			   while not (StatePairSet.is_empty !same_pair)  do
  				let (start_loop,end_loop) = StatePairSet.min_elt !same_pair in
  				let tail = ref end_loop in
  				same_pair := StatePairSet.remove (start_loop,end_loop) !same_pair;
  				StatePairSet.iter (fun (a,b) ->  if a = (!tail)
  				                                  then begin
																								   tail := b;
  																					     same_pair := StatePairSet.remove (a,b) !same_pair
																									 end
																							else ()
  																						 ) 	!same_pair 
																								;
					 let end_loop = end_loop-1 in
					 tail := (!tail+end_loop-start_loop+1);
					 if start_loop=end_loop 
					   then ()
						 else loop_f := LoopSet.add (start_loop,end_loop,!tail) !loop_f
					 
				 done
				end
				;
			(*	Printf.printf "%s" "********************** 可以泛化的循环 *******************************************\n";
        LoopSet.iter (fun (a,b,c)  -> Printf.printf "%d," ( a );
                              Printf.printf "%d," ( b );
															Printf.printf "%d\n" c  ) !loop_f  ;
                     flush stdout;  *)
		
		
	let num = ref 0 in				
	let tran = ref TranSet.empty in 
	
	let start_loop_state = ref (-1) in
	let end_loop_state = ref (-1) in
	
	let start_loop = ref (-1) in
	let end_loop = ref (-1) in
	let tail = ref (-1) in
  if (LoopSet.is_empty !loop_f ) then ()
	                               else begin
																	    let (start_loop_1,end_loop_1,tail_1) = LoopSet.min_elt !loop_f in
																      start_loop := start_loop_1;
																			end_loop := end_loop_1;
																			tail := tail_1;
																			loop_f := LoopSet.remove (start_loop_1,end_loop_1,tail_1) !loop_f
																			end
	                               ;
	    
	   	Array.iteri ( fun i instr ->
				                 if !start_loop = (-1) 
												   then begin
														    tran := TranSet.add (!num, instr, !num+1) !tran;
													      num := !num+1
																end
									 else  if i = (!start_loop)
											     then begin
														   tran := TranSet.add (!num, instr, !num+1) !tran;
													     start_loop_state := !num;
															 num := !num+1
															 end														     
									 else  if i = (!end_loop) 
													 then begin 
										           tran := TranSet.add (!num, instr, !start_loop_state) !tran;
									             end_loop_state := !num
														   end
								   else  if i = ( !tail )
													 then begin
														   tran := TranSet.add (!start_loop_state,instr,!num+1) !tran;
													     num := !num+1;
															 if (LoopSet.is_empty !loop_f ) then ()
					                               else begin
																					    let (start_loop_1,end_loop_1,tail_1) = LoopSet.min_elt !loop_f in
																				      start_loop := start_loop_1;
																							end_loop := end_loop_1;
																							tail := tail_1;
																							loop_f := LoopSet.remove (start_loop_1,end_loop_1,tail_1) !loop_f
																							end  
															 end
									 else  if i < (!end_loop)
												   then begin
														     tran := TranSet.add (!num, instr, !num+1) !tran;
															   num := !num+1
															  end
									 else  if  ( i > (!tail) ) 
													 then  
															 begin
															   tran := TranSet.add (!num, instr, !num+1) !tran;                                   (*相邻两个循环可能会有问题    目前的程序中一般不会出现   需要注意*)
																 num := !num+1																				 
																	 end
											 else ()       ) execution
								       ;
																												
			let start = 0 in
			let receive = NumSet.add !num  NumSet.empty in	
			
			if (!not_end)
			   then  InstrSet.iter (fun instr ->
					               tran := TranSet.add (!num,instr,!num) !tran
				                   ) instr_set
		  ;
			let tran = 	Automata.tranSet_to_tranMap !tran	in
		  {start;receive;tran}		
		end								
else 
		let tran = ref TranSet.empty in 	
		let num = ref 0 in			
    Array.iter (fun instr ->
			               tran := TranSet.add (!num,instr,!num+1) !tran;
										 num := !num+1    )  execution
										;
		if (!not_end)
			   then  InstrSet.iter (fun instr ->
					           tran := TranSet.add (!num,instr,!num) !tran
				                   ) instr_set
		  ;
	  let tran = Automata.tranSet_to_tranMap !tran in
    let receive = NumSet.add (!num) NumSet.empty in
		{start=0; receive; tran}

(*------------------------------------------------------------------------- 对不相关语句的泛化  ----------------------------------------------------------------------------*)

(*得到与结果相关的变量*)
let rec get_re_var  execution re_var_temp re_var_set = 
          Array.iter (fun instr ->   
					    let (m,n)	= Execution.get_var_instr instr in
							 if (re_var_temp=m && re_var_temp!=n)
								  then begin 
										    let length1 = StringSet.cardinal !re_var_set in
										    re_var_set := StringSet.add n !re_var_set;
												if length1 = (StringSet.cardinal !re_var_set)
												   then ()
									         else get_re_var  execution n re_var_set    
									     end
							 else if re_var_temp=n && re_var_temp!=m
							    then begin 
										    let length1 = StringSet.cardinal !re_var_set in
										    re_var_set := StringSet.add m !re_var_set;
												if length1 = (StringSet.cardinal !re_var_set)
												   then ()
									         else get_re_var  execution m re_var_set 
										       
									     end
							 else ()
							 ;                     	) execution

(*得到与结果无关的所有指令*)																	
let get_ir_instr x instr_set execution = 
	  let re_var_set = ref StringSet.empty in
	  get_re_var  execution x re_var_set;
		InstrSet.fold (fun instr ir_instr -> 
			                 let (m,n)	= match instr with 
					             | Execution.AssignFromLocToLoc (x0,f,y0) -> (x0, Execution.string_of_list y0)
							         | Execution.AssignFromLoc (x0,y0) -> (x0,y0)
											 | Execution.AssumeLocEq (x0,y0) -> (x0,y0)
											 | Execution.AssumeLocNeq (x0,y0) -> (x0,y0)
											 | _ ->  begin assert false  end
																    in
											if not (StringSet.mem m !re_var_set) && not (StringSet.mem n !re_var_set)
												 then InstrSet.add instr  ir_instr
												 else ir_instr
												)  instr_set InstrSet.empty 
		

(*对结果无影响的语句的泛化*)
let rec irrelevant_refin_auxi  automata_temp q0 tran ir_instr_set tran_set have_skip =  
	  
		let coset = TranMap.find q0 automata_temp.tran in
		if (CoSet.is_empty coset)  
		   then   
				   ()
			 else
				   CoSet.iter (fun (instr,q1) -> 
				                   if  (q0 != q1) && not (NumSet.mem q1 automata_temp.receive) && not (TranSet.mem (q0,instr,q1) !tran_set)  
													    then  begin
																      tran_set := TranSet.add (q0, instr, q1) !tran_set;
																      let succ_q1 = Automata_utils.get_succ  q1 automata_temp.tran in
																			if (*not (NumSet.mem q0 succ_q1) && *) (InstrSet.mem instr ir_instr_set)
  																			 then   begin
  																					    let coset = CoSet.remove (instr,q1) coset in
																							  (* let coset = CoSet.add (instr,q0) coset in *)																
																							  let coset = InstrSet.fold (fun instr coset -> 
																									                             CoSet.add (instr,q0) coset     ) ir_instr_set coset in 
  																							let coset = CoSet.add (Execution.Skip,q1) coset in
  																							have_skip := true;
  																							tran := TranMap.add q0 coset !tran;
  																							irrelevant_refin_auxi  automata_temp q1 tran ir_instr_set  tran_set have_skip
  																					    end
																				 else   
																					     (* let coset = InstrSet.fold (fun instr coset -> 
																			                             CoSet.add (instr,q0) coset     ) ir_instr_set coset in  
																		              tran := TranMap.add q0 coset !tran;  *)
																					      irrelevant_refin_auxi  automata_temp q1 tran ir_instr_set  tran_set have_skip
																    end
															else  ()    ) coset

let irrelevant_refin  automata have_skip ir_instr_set =
    let tran_set = ref TranSet.empty in  (*防止进入循环出不来*)
    let tran = ref automata.tran in
    irrelevant_refin_auxi  automata automata.start tran ir_instr_set tran_set have_skip;
    {start=automata.start;receive=automata.receive;tran=(!tran)}


(*------------------------------------------------------------------------去掉不相关语句得到语句序列------------------------------------------------------------------------*)
let remove_irrelevant  execution ir_instr_set = 		  									
		Array.fold_left (fun execution_result instr -> 
			                  if not (InstrSet.mem instr ir_instr_set) 
												   then Array.append execution_result [|instr|]
													 else execution_result )	[||] execution 

(*-------------------------------------------------------------------------  gen_loop  -------------------------------------------------------------------------------*)			
let  gen_automata_mixture_other  execution ir_instr_set instr_set =
	   let (var_list,fun_list) = Coherence.get_var_fun  execution in
	   let automata_temp = gen_loop 	execution var_list fun_list	instr_set in
			 (* Printf.printf "----------- 泛化出循环之后 -------------\n";
		  Automata.tranMap_visualize automata_temp.tran;  
		  flush stdout;  *)

(*		          		(*对不相关的语句进行泛化*)
  		let instr_end = execution.( (Array.length execution) - 1 ) in																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																					
  		let (x,y) = match instr_end	 with 
  	             	| Execution.AssumeLocEq (x,y)	 -> (x,y)
  								| Execution.AssumeLocNeq (x,y)	-> (x,y)
  								| _ -> assert false
  						in
*)
  		             				
  		let have_skip = ref false in
  		let automata_temp = irrelevant_refin   automata_temp  have_skip  ir_instr_set in
			
  	  if (!have_skip)
  		   then  Automata_utils.automata_remove_eplision 	automata_temp					 
  		 	 else  automata_temp


(*------------------------------------------------------------- 对遇到冲突状态情况的泛化 -------------------------------------------------------------------------------------*)
(*
(*遇到冲突状态的泛化  冲突状态在结尾的情况不进行泛化  *)
let rec refin_conlict_auxi  point  state_tri_temp tran tran_set automata receive instr_set = 
	
	  if (State.is_conflict state_tri_temp) && not (NumSet.mem point automata.receive)
		   then  begin
				       
				       let coset0 = InstrSet.fold (fun instr coset0 ->
								                                CoSet.add (instr,point) coset0  ) instr_set CoSet.empty in
							 tran := TranMap.add point coset0 !tran;
							 receive := NumSet.add point !receive;									 			 
				     end
			 else   let coset0 = TranMap.find point automata.tran in
				      if (CoSet.is_empty coset0)  
		             then  ()
			           else  
									    CoSet.iter (fun (instr,q1) ->
	                     if (TranSet.mem (point,instr,q1) !tran_set) 
											    then  ()
													else  begin
														    tran_set := TranSet.add  (point,instr,q1) !tran_set;
													      let  state_tri_next = State.refresh_state state_tri_temp instr in
																refin_conlict_auxi   q1 state_tri_next tran tran_set automata receive instr_set
															  end
																) coset0

let refin_conlict automata var_list fun_list instr_set = 
	  let state_tri_begin = State.init var_list fun_list in	
		let tran_set = ref TranSet.empty in  (*防止进入循环出不来*)
    let receive = ref (NumSet.empty) in
    let tran = ref (automata.tran) in
    refin_conlict_auxi 	automata.start state_tri_begin tran tran_set automata receive instr_set;
    let tran = Automata_utils.delete_useless_state  !tran !receive in
    {start=automata.start;receive=(!receive);tran=tran}		
		*)										
(*---------------------------------------------------------------------- 对coherent情况的泛化  -------------------------------------------------------------------------------*)

(*
(*对于coherent路径的不动点泛化*)
let fixpoint  execution state_array ir_instr_set = 

	let num = ref 0 in	
(*	Printf.printf "-----------------------------------------------------------------\n";
	Array.iter (fun state -> visualize state  ) state_array;
	flush stdout;  *)
	
	let receive = ref NumSet.empty in
	let coset0 = InstrSet.fold (fun instr coset_next ->
																	CoSet.add (instr,!num) coset_next
																		 ) ir_instr_set CoSet.empty in 
																		
																		
	let tran = ref (TranMap.add 0 coset0 TranMap.empty) in
	let state_set = ref ( StateSet.add (!num,state_array.(0) ) StateSet.empty ) in
	Array.iteri (fun i instr ->
		                  let state_that = StateSet.find (-2,state_array.(i) ) !state_set in			
																																								 
											let that_key = match state_that with
										                	|(key,state) ->  key  in 											
											let state_find = StateSet.find_opt (-2,state_array.(i+1) ) !state_set in
										  let next_key = match state_find with
                											| None -> (-1)
                											| Some (key,state) ->  key  in 
										  let coset = TranMap.find that_key (!tran) in											
										  if next_key = (-1)
											   then begin									
													      num := !num+1;	       															
																let coset = CoSet.add (instr,!num) coset in
																tran := TranMap.add that_key coset !tran;																	
																if ( State.is_conflict state_array.(i+1) ) 
																   then begin 
																		       receive := NumSet.add !num !receive;
																					 tran := TranMap.add !num CoSet.empty !tran;	
																	      end 
																	 else begin
																		    let coset_next = InstrSet.fold (fun instr coset_next ->
																		                          CoSet.add (instr,!num) coset_next
																											            ) ir_instr_set CoSet.empty in 
																				
																				tran := TranMap.add !num coset_next !tran	
																				end
																	;														
																state_set := StateSet.add (!num,state_array.(i+1)) !state_set
													    end
												 else begin
															let coset = CoSet.add (instr,next_key) coset in
															tran := TranMap.add that_key coset !tran	
															end																					 																								
											 ) execution ;									
	  {start=0;receive=(!receive);tran=(!tran)}					
*)


let fixpoint_conlict  execution state_array ir_instr_set instr_set flag = 
	let num = ref 0 in	
 (*	Array.iter (fun state -> State.visualize state  ) state_array;  *)
	let receive = ref NumSet.empty in
	let coset0 = InstrSet.fold (fun instr coset_next ->
																	CoSet.add (instr,!num) coset_next
																		 ) ir_instr_set CoSet.empty in 		
(*	let coset0 = CoSet.empty in		*)											
																		
	let tran = ref (TranMap.add 0 coset0 TranMap.empty) in
	let state_set = ref ( StateSet.add (!num,state_array.(0) ) StateSet.empty ) in
	let is_end = ref false in
	Array.iteri (fun i instr ->
		            if !is_end
								   then ()
									 else 
		                  let state_that = StateSet.find (-2,state_array.(i) ) !state_set in			
																																								 
											let that_key = match state_that with
										                	|(key,state) ->  key  in 											
											let state_find = StateSet.find_opt (-2,state_array.(i+1) ) !state_set in
										  let next_key = match state_find with
                											| None -> (-1)
                											| Some (key,state) ->  key  in 
										  let coset = TranMap.find that_key (!tran) in											
										  if next_key = (-1)
											   then begin									
													      num := !num+1;	       															
																let coset = CoSet.add (instr,!num) coset in
																tran := TranMap.add that_key coset !tran;																	
																if ( State.is_conflict state_array.(i+1) ) 
																   then begin 
																		       receive := NumSet.add !num !receive;
																					 let coset = if (i = (Array.length execution -1) ) && flag 
																					                then  CoSet.empty
																													else  InstrSet.fold (fun instr coset ->
																	                                 CoSet.add (instr,!num) coset    ) instr_set  CoSet.empty in 
																					 tran := TranMap.add !num coset !tran;																					 	
																					 is_end := true;
																	      end 
																	 else begin
																		    let coset_next = InstrSet.fold (fun instr coset_next ->
																		                          CoSet.add (instr,!num) coset_next
																											            ) ir_instr_set CoSet.empty in 
																				tran := TranMap.add !num coset_next !tran	
																				end
																	;														
																state_set := StateSet.add (!num,state_array.(i+1)) !state_set
													    end
												 else begin
															let coset = CoSet.add (instr,next_key) coset in
															tran := TranMap.add that_key coset !tran	
															end																					 																								
											 ) execution ;									
	  {start=0;receive=(!receive);tran=(!tran)}		

(*---------------------------------------------------------------------- 对 early_assume 情况的泛化  -------------------------------------------------------------------------------*)	
let gen_automata_ear   execution assume_instr insert_location ir_instr_set instr_set =		
		let (var_list,fun_list) = Coherence.get_var_fun execution in
		let state_temp = ref (init var_list fun_list) in
		let change_array = ref  (Array.append  [||] [|!state_temp|]) in
		Array.iteri (fun i instr ->
                  state_temp := refresh_state !state_temp instr;									
											if i = insert_location
											   then  begin
													     (*根据state1对state_temp进行改造*)
															 let state1 = refresh_state !state_temp assume_instr  in 
															 let (x,y) = Execution.get_var_instr	assume_instr in
															 let x = var_of_string x in
															 let y = var_of_string y in
															(* let eq = PairSet.fold (fun (a,b) eq ->												                       
																                       if not (compare_var a x = 0 ) && not (compare_var a y = 0 ) && not (compare_var b x = 0 ) && not (compare_var b y = 0)
																											    then  PairSet.add (a,b) eq 																												 
																													else eq ) state1.eq PairSet.empty   in			
																													
															 let dq = PairSet.fold (fun (a,b) dq ->																                       
																                       if not (compare_var a x = 0 ) && not (compare_var a y = 0 ) && not (compare_var b x = 0 ) && not (compare_var b y = 0)
																											    then PairSet.add (a,b) dq
																													else dq  )  state1.dq PairSet.empty  in
																														
															 let fun_set = TripleSet.fold (fun (f,a,b) fun_set ->		
																                              let x0 = Depvar x in
																															let y0 = Depvar y in	
																                              if not (compare_var a x = 0 ) && not (compare_var a y = 0 ) && not (compare_dep_var b x0 = 0 ) && not (compare_dep_var b y0 = 0)
																															   then TripleSet.add (f,a,b) fun_set
																																 else TripleSet.add (f,a,Undef) fun_set    )  state1.fun_set TripleSet.empty in			
															 let item = ItemSet.empty in
															 state_temp := {eq;dq;fun_set;item};   *)
															 
															 let eq = if  PairSet.mem (x,y) !state_temp.eq
																								             then state1.eq   
																														 else  begin
																															      let eq_temp = PairSet.remove  (x,y) state1.eq  in
																																		let eq_temp = PairSet.remove (x,y) eq_temp in
																																		PairSet.remove (y,x) eq_temp
																																	 end         in
															
															 state_temp := {eq;dq=state1.dq;fun_set=state1.fun_set;item=state1.item};
															 change_array := Array.append !change_array [|!state_temp|]									           
															 end
												 else  change_array := Array.append !change_array [|!state_temp|]											
                  ) execution ;
	  fixpoint_conlict  execution !change_array ir_instr_set instr_set true



(*---------------------------------------------------------------------- 对 memorizing 情况的泛化  -------------------------------------------------------------------------------*)	

let delete_ghost  state_array ghost_set =
		 let start_map = ref Gmap.empty in
		 let end_map = ref Gmap.empty in
		 StringSet.iter (fun ghost ->
			                  start_map := Gmap.add ghost (-1) !start_map;
												end_map := Gmap.add ghost (-1) !end_map  ) ghost_set;
		 
		 Array.iteri(fun i state ->
			         PairSet.iter(fun (x,y) ->
									let ghost = ref "" in
									(*获取 ghost 变量的名字*)
									if (String.equal (String.sub (string_of_var x) 0 1)  "@" ) && not (String.equal (String.sub (string_of_var y) 0 1)  "@" )
							  	     then begin  ghost := string_of_var x   end  
									else  if (String.equal (String.sub (string_of_var y) 0 1)  "@" ) && not (String.equal (String.sub (string_of_var x) 0 1)  "@" )     
										   then begin ghost := string_of_var y  end  ;								
						
						      if !ghost != ""
									   then begin
											      let loc_start = Gmap.find !ghost !start_map in
									          let loc_end = Gmap.find !ghost !end_map in
									          if  loc_start = (-1)
									              then  begin start_map := Gmap.add !ghost i !start_map end;
									          if loc_end < i
									              then  begin end_map := Gmap.add !ghost i !end_map end 
											    end						     
                ) state.eq    ) state_array;														

			StringSet.iter (fun ghost ->
				                let start = Gmap.find ghost !start_map  in
												let end_ =  Gmap.find ghost !end_map in										
												Array.iteri (fun i state ->         																
          																if start < i && i <= end_
          																   then    begin
          																		           let flag = ref true in 
          																		           PairSet.iter (fun (x,y) -> 
          																								      if   (String.equal (string_of_var x) ghost ) || (String.equal (string_of_var y) ghost  )
          																											    then  flag := false
          																								          ) state.eq;
          																							 if !flag
          																							    then  end_map := Gmap.add ghost (i) !end_map
          																									
          																		       end      ) state_array  	) ghost_set;

			let state_array_new = ref [||] in
		  Array.iteri (fun i state0  ->  				
      	    let state_new =  StringSet.fold(fun g0  state ->
      										   let start_loc = Gmap.find g0 !start_map in
      											 let end_loc = Gmap.find g0 !end_map in
      											  if  i < start_loc || i > end_loc
      											    then   begin
      														     let eq = PairSet.fold (fun (x,y) eq ->
      																	           if String.equal   (string_of_var x)   g0 ||  String.equal   (string_of_var y)  g0 
                      							                  then  eq
                      								                else  PairSet.add (x,y) eq        ) state.eq PairSet.empty in
      																
      														     let dq = PairSet.fold (fun (x,y) dq ->
                                          if String.equal   (string_of_var x)   g0 ||  String.equal   (string_of_var y)  g0 
                      							           then  dq
                      								         else  PairSet.add (x,y) dq      ) state.dq  PairSet.empty  in
      																				
      																 let fun_set = TripleSet.fold (fun (f,x,y)  fun_set ->								
                    	                    if  String.equal (string_of_dep_var y)  g0  &&  not (String.equal (String.sub (string_of_var x) 0 1)  "@" )
      																		    then   TripleSet.add (f,x,Undef) fun_set																			 
      																			  else  if String.equal  (string_of_var x)  g0 || String.equal  (string_of_dep_var y)  g0
      																		           then  fun_set
                    								                 else  TripleSet.add (f,x,y) fun_set  ) state.fun_set  TripleSet.empty  in 																																											
      																	   {eq;dq;fun_set;item=ItemSet.empty}
      															    end
      													 else   state	
      														           ) ghost_set  state0   in
																						
      				state_array_new := Array.append   !state_array_new	 [|state_new|]  																					
																) state_array;
																
		    (*给ghost变量改名  避免出现无限循环的情况 *)														
	(*				 let count = ref 0 in
					 Array.iter ( fun state ->
						          let g_set = ref StringSet.empty in
											PairSet.iter(fun (x,y) ->
												               if (String.equal (String.sub (string_of_var x) 0 1)  "@" )
																			    then g_set := StringSet.add (string_of_var x) !g_set;
																			 
																			 if (String.equal (String.sub (string_of_var y) 0 1)  "@" )
																			    then g_set := StringSet.add (string_of_var y) !g_set;
																					
												               ) state.eq;
																			
											PairSet.iter(fun (x,y) ->
												               if (String.equal (String.sub (string_of_var x) 0 1)  "@" )
																			    then g_set := StringSet.add (string_of_var x) !g_set;
																			 
														state_array					 if (String.equal (String.sub (string_of_var y) 0 1)  "@" )
																			    then g_set := StringSet.add (string_of_var y) !g_set;
												              
												                 ) state.eq;
																				
											TripleSet.iter(fun (f,x,y) ->
												               if  (String.equal (String.sub (string_of_var x) 0 1)  "@")
																			     then  g_set := StringSet.add (string_of_var x) !g_set;
																			 if  (String.equal (String.sub (string_of_dep_var y) 0 1)  "@")
																			     then  g_set := StringSet.add (string_of_dep_var y) !g_set;
																				
												                 ) state.fun_set;
																				
											count := 	StringSet.cardinal 	!g_set;	
																		
						                 ) !state_array_new;				*)
							
						 		
																															
	      !state_array_new
													
	    
(*memorizing情况的泛化*)
let gen_automata_mem  execution ir_instr_set instr_set =
	   let execution_co = Coherence.make_mem_coherent execution in
		 let ghost_set = Array.fold_left (fun ghost_set instr  ->
			                                    let (x,y) = Execution.get_var_instr instr in
																					if (String.equal (String.sub x 0 1)  "@" )
																					   then  StringSet.add x ghost_set
																						 else  ghost_set                  ) StringSet.empty  execution_co in
																						
     let state_array_temp = Coherence.get_state_array  execution_co in
		(* Array.iter (fun state -> State.visualize state  ) state_array_temp; *)

		
		 let num = ref (1) in
		 let state_array_new = ref [| state_array_temp.(0) |] in
     Array.iteri (fun i state ->
			           if i > 0
								    then begin
      											let (x,y) =  Execution.get_var_instr execution_co.(!num-1) in  														
            							  num := !num+1;
            								if (String.equal (String.sub x 0 1)  "@" )
            								   then  begin
      													       let temp = Array.sub !state_array_new  0  ( Array.length !state_array_new -1 ) in
            												   state_array_new := Array.append 	temp [|state|]
            												 end 										   
            									 else  state_array_new := Array.append  !state_array_new [|state|]  										
											   end
      								          ) state_array_temp ;
														
		let state_array_new =  delete_ghost  !state_array_new ghost_set in
		
	(*	Array.iter (fun state -> State.visualize state  ) state_array_new; *)
			
		fixpoint_conlict  execution state_array_new ir_instr_set instr_set true	
		
																								
(*---------------------------------------------------------------------- early_assume和memorizing都出现时的泛化  -------------------------------------------------------------------------------*)		

let  gen_automata_mixture  execution_old state_array ir_instr_set instr_set = 
	   let execution = remove_irrelevant  execution_old ir_instr_set in																																												
																																																																														
     let assume_instr = ref (Execution.Skip) in
  	 let location = ref 0 in   (*违反 early assume的位置 *)
     Array.iteri (fun i instr ->				
  					match instr with							
  					| Execution.AssumeLocEq (x,y) -> 
  						   if (Coherence.check_early_assume  state_array.(i) (x,y) ) 
  							       then begin  
  											       assume_instr := Execution.AssumeLocEq (x,y); 
  														 location := i
  													end
  							 else ()						
  					| _ -> ()
  					;      			
  			       ) execution
  					;
		(* Printf.printf "%s\n" (Execution.string_of_instr !assume_instr) ;  *)
     let (execution_ahead,insert_location) = Coherence.assume_ahead   execution state_array !assume_instr !location in
  	(*  Printf.printf "------------------------- assume提前之后 -------------------------------\n";
  	 Array.iter (fun instr -> Printf.printf "%s\n" (Execution.string_of_instr instr)  ) execution_ahead;  *)
		 let execution_ahead_state = Coherence.get_state_array  execution_ahead in
		 let (v_mem,v_ear) = Coherence.is_coherence  execution_ahead  execution_ahead_state  in
		 if v_ear=0  && v_mem=0
		   then  begin  
			       (*  Printf.printf "class:2\n";  
							 flush stdout;  *)
							 let result = gen_automata_ear  execution !assume_instr insert_location ir_instr_set instr_set in
							 (result,2) 
						 end
		 else if  v_ear=1			
		   then  begin (* Printf.printf "class:4\n";  
			              flush stdout; *)
			             (* Array.iter (fun instr ->
											         Printf.printf "%s\n"  (Execution.string_of_instr instr)  ) execution_ahead;  *)
									 let result = gen_automata_mixture_other  execution_old  ir_instr_set instr_set in
									 (result,3)
							end
			 else  let execution_co_temp = Coherence.make_mem_coherent execution_ahead in
			     (*  Printf.printf "class:3\n"; 	
						 flush stdout;  *)
						 let ghost_set = Array.fold_left (fun ghost_set instr  ->
	                                    let (x,y) = Execution.get_var_instr instr in
																			if (String.equal (String.sub x 0 1)  "@" )
																			   then  StringSet.add x ghost_set
																				 else  ghost_set                  ) StringSet.empty  execution_co_temp in
																				
		       (* StringSet.iter (fun g0 ->  Printf.printf "ghost:%s\n" g0  ) ghost_set;	*)
						
						(* Printf.printf "------------------------- execution_co_temp -------------------------------\n";
  		       Array.iter (fun instr -> Printf.printf "%s\n" (Execution.string_of_instr instr)  ) execution_co_temp;  *)
						 (*将路径中被提前的 assume 语句   移动到原来位置   *)
						 let insert_location_co = ref (-1) in
						 let execution_co = ref [||] in
						 let num = ref 0 in
						 Array.iteri (fun i instr ->
                                if (Execution.compare_instr  execution.(!num) instr )=0
																   then begin
																		      execution_co := Array.append !execution_co [|instr|];
																					num := !num+1
																		    end
																	 else if  (Execution.compare_instr  !assume_instr instr )=0
																        then  insert_location_co := i-1
																	 else if  (Execution.compare_instr  execution.(!num) !assume_instr )=0
																				then begin	
																					     execution_co := Array.append !execution_co [|!assume_instr|];
																							 num := !num +1;
																							 if (Execution.compare_instr  execution.(!num) instr )=0
																							     then begin execution_co := Array.append !execution_co [|instr|]; num := !num+1 end
																									 else begin execution_co := Array.append !execution_co [|instr|]   end
																				     end
																	 else  execution_co := Array.append !execution_co [|instr|]																					      
																	         )  execution_co_temp
              ;
							if  (Array.length  !execution_co) = ( (Array.length execution_co_temp)-1 )  &&  ((Execution.compare_instr  execution.(Array.length execution -1) !assume_instr )=0)
							    then   execution_co := Array.append !execution_co [|!assume_instr|] 
							;
							
						(*	Printf.printf "----------------------- execution_co_lalala ----------------------------\n";
							Printf.printf "location:%d\n"  !insert_location_co;
							Array.iter (fun instr -> Printf.printf "%s\n" (Execution.string_of_instr instr)  ) !execution_co   ;   *)
							
              let (var_list,fun_list) = Coherence.get_var_fun !execution_co in
		          let state_temp = ref (init var_list fun_list) in							
							
							(*将 assume 信息提前所拿到的 信息加入得到的序列*)
		          let change_array = ref  [|!state_temp|] in
							Array.iteri (fun i instr ->
						               let (x,y) = Execution.get_var_instr instr in
													 state_temp := refresh_state !state_temp instr;
									         if i=(!insert_location_co)
														  then  begin
																      let state1 = refresh_state  !state_temp !assume_instr in
																			let (x,y) = Execution.get_var_instr	!assume_instr in
        															let x = var_of_string x in
        															let y = var_of_string y in
																			let eq = if  PairSet.mem (x,y) !state_temp.eq
																			             then state1.eq   
																									 else  begin
																										      let eq_temp = PairSet.remove  (x,y) state1.eq  in
																													PairSet.remove (x,y) eq_temp 
																												 end         in
										                  state_temp := {eq;dq=state1.dq;fun_set=state1.fun_set;item=state1.item};																							
																			change_array := Array.append !change_array [|!state_temp|];
																	(*	Printf.printf "----------------------------- %s ------------------------------------------\n" ( Execution.string_of_instr  instr ) ;
																			State.visualize state  *)
																    end       
															else   begin
															       change_array := Array.append !change_array [|!state_temp|];
																		end
															           ) !execution_co
																	   ;
							(*将不用的 ghost 变量删除  得到的状态序列*)							
							let num = ref (1) in
		          let state_array_new = ref [|!change_array.(0)|] in
              Array.iteri (fun i state ->
			           if i > 0
								    then begin
      											let (x,y) =  Execution.get_var_instr !execution_co.(!num-1) in  														
            							  num := !num+1;
            								if (String.equal (String.sub x 0 1)  "@" )
            								   then  begin
      													       let temp = Array.sub !state_array_new  0  ( Array.length !state_array_new -1 ) in
            												   state_array_new := Array.append 	temp [|state|]
            												 end 										   
            									 else  state_array_new := Array.append  !state_array_new [|state|]  										
											   end
      								          ) !change_array ;
														
		         let state_array_new =  delete_ghost  !state_array_new ghost_set in																
																	
					(*		Array.iter (fun instr -> Printf.printf "\n%s\n" (Execution.string_of_instr instr)  ) execution;							
																																						
							Printf.printf "execution_length:%d\n" (Array.length execution);
							Printf.printf "State_array_length:%d\n" (Array.length !change_array);
							Array.iteri (fun i state ->  
								              if (i > 0)
															   then   Printf.printf "----------------------------- %s ------------------------------------------\n" ( Execution.string_of_instr execution.(i-1) )																	    
																 else   Printf.printf "-----------------------------------------------------------------------------------\n" ;
															State.visualize state   ) !change_array;    *)
						
							
							let result = fixpoint_conlict  execution state_array_new ir_instr_set instr_set true in
							(result,3)


(*-----------------------------------------------------  对抽取的路径进行泛化   分为三种情况 1、coherent的路径  2、只有early_assume的路径  3、含有memorizing情况的路径 --------------------------------------------*)		
let gen_automata   execution_old var_list fun_list instr_set is_feasible = 
  
	  (* let re_var = Execution.get_re_var env prog in  *)

  	let instr_end = execution_old.(Array.length execution_old - 1) in	
	  let (x,y) = match instr_end	 with 
        	             	| Execution.AssumeLocEq (x,y)	 -> (x,y)
        								| Execution.AssumeLocNeq (x,y)	-> (x,y)
        								| _ -> assert false
        						in
	if (is_feasible = 1)
	   then begin		   			  
			      let state_array = Coherence.get_state_array  execution_old in					
	          let result = fixpoint_conlict  execution_old state_array InstrSet.empty instr_set false in  
	          (* Printf.printf "not_end\n";  *)
	          (result,4)
			    end
		 else 		       
      	  let ir_instr_set = get_ir_instr  x instr_set execution_old in 	
      		(*删掉不相关语句后的序列*)
      	  let execution = remove_irrelevant  execution_old ir_instr_set in	 
      		
      	(*  Printf.printf "---------------------- 去掉不相关语句 -------------------------\n";
      		Array.iter (fun instr -> Printf.printf "%s\n" (Execution.string_of_instr instr)  ) execution;
      		Printf.printf "------------------------------------------------------------\n";  *)
			    
      		let state_array = Coherence.get_state_array  execution in
      	(*	Array.iter (fun state -> State.visualize state  ) state_array;  *)
      	  																			
					let new_refin = true in				
					if new_refin 
					   then begin   
							      if (is_feasible = 2)
										   then begin
												      let result = fixpoint_conlict  execution state_array ir_instr_set instr_set true in
															(result,0)
												    end
											 else begin
												       let (v_mem,v_ear) = Coherence.is_coherence  execution state_array in
            									 (*	 Printf.printf "v_mem:%d\n" v_mem;
            										 Printf.printf "v_ear:%d\n" v_ear; *)
                      				   if v_mem=0 && v_ear=0
                      					    then  begin   
      																			 let result = fixpoint_conlict  execution state_array ir_instr_set instr_set true in
      															         (result,0)     											
																					end					            												    
                      					 else if v_ear=0 && v_mem=1
                      					    then  begin  
            													      (* Printf.printf "class:1\n"; *)
            																 flush stdout;
            																 let result = gen_automata_mem   execution ir_instr_set instr_set in
            																 (result,1)
            															end
                      					 else    gen_automata_mixture   execution_old  state_array  ir_instr_set instr_set					      
												    end 
											       
			     end 
					  else (gen_automata_mixture_other    execution_old	 ir_instr_set instr_set ,0)
					
			
		
			
	