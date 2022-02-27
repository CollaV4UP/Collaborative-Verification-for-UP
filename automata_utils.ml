open Automata
open OCamlFlat
(*---------------------------------------------- 适配以调用OCamlFlat的接口 --------------------------------------------------------------------*)

module InstrMap = Map.Make(
	struct 
		type t = Execution.instr
	  let  compare = Stdlib.compare
	end)
type instr_char_map = char InstrMap.t

module CharInstrMap = Map.Make(
	struct 
		type t = char
	  let  compare = Stdlib.compare
	end)
type char_instr_map = Execution.instr CharInstrMap.t
	
module StateNumMap = Map.Make(
	struct 
		type t = string
	  let  compare = Stdlib.compare
	end)
type state_num_map = int StateNumMap.t

(*let numset_compare v1 v2 = *)
	  

(*StateSet和num之间的map  在确定化的时候用于存储已经产生的状态*)
module StateSetNumMap = Map.Make(
	struct 
		type t = NumSet.t
	  let  compare = Stdlib.compare
	end)
type stateSet_num_map = int StateSetNumMap.t 

module StateSet = Set.Make(
  struct
    type t =  NumSet.t
    let compare = Stdlib.compare
  end)

(*自动机求交时存储已产生的状态*)
module StateTripleSet = Set.Make(
  struct
    type t =  int*int*int
    let compare (v1,v2,v3) (v4,v5,v6) = compare_pair (v2,v3) (v5,v6)
  end)


(*适配OCamlFlat方法的接口  choose： 1#确定化 2#最小化 3#去除无用状态  4#确定化并且最小化 5#变成json格式输出*)	
let ocamlflat_utils automata instr_set choose = 
  
	(*将自动化机转为json字符串的形式*)
  	let instr_char = ref '0' in
  	(*  instr_char_map : instr -> char  用于适应OCamlFlat接口
  	    char_instr_map : char -> instr  用于将OCamlFlat格式的转换成 需要的格式
  	   *)
    let (instr_char_map,char_instr_map) = InstrSet.fold (fun instr (instr_char_map,char_instr_map) -> let instr_char_map = InstrMap.add instr !instr_char instr_char_map in
  	                                                                                                let char_instr_map = CharInstrMap.add !instr_char instr char_instr_map in
  	                                                      let int_c = int_of_char !instr_char in																										
  																											  instr_char := char_of_int (int_c + 1);
  																											  (instr_char_map,char_instr_map)  ) instr_set (InstrMap.empty,CharInstrMap.empty) in
  																																																						
  	let instr_char_map = InstrMap.add Execution.Skip epsilon instr_char_map in	
  	let char_instr_map = CharInstrMap.add epsilon Execution.Skip 	char_instr_map in																	
	
  let kind = "kind : \"finite automaton\",\n" in
	let description  = "description : \"this is an example\",\n" in
	let name = "name : \"big_automata\",\n" in
	
	(*转换字母表为json字符串*)
	let instr_set_temp = ref instr_set in
	let min_elt = InstrSet.min_elt  !instr_set_temp in
	let alphabet = ref ("alphabet : ["^"\""^(Char.escaped (InstrMap.find  min_elt instr_char_map))^"\""  ) in
	instr_set_temp := InstrSet.remove min_elt !instr_set_temp;
	while  not (InstrSet.is_empty !instr_set_temp) do
		     let min_elt = InstrSet.min_elt  !instr_set_temp in
		     alphabet := !alphabet^","^"\""^(Char.escaped (InstrMap.find  min_elt instr_char_map))^"\"";
				 instr_set_temp := InstrSet.remove min_elt !instr_set_temp;				
		done ;
	alphabet := !alphabet^"],\n";
	
	(*转换状态为json格式*)
	let state =  ("states : ["^"\"0\"") in
	let state_set = TranMap.fold (fun q0 coset state_set -> NumSet.add q0 state_set ) automata.tran NumSet.empty 	in
	let state_set = NumSet.remove 0 state_set in
	let state = NumSet.fold (fun q0 state ->  state^","^"\""^(Core.Int.to_string q0)^"\"" ) state_set  state in
  let	state = state^"],\n" in
	
	let initialState = "initialState : "^"\""^(Core.Int.to_string automata.start)^"\",\n" in
	
  (*转换迁移为json格式*)	
	let transitions = "transitions : [\n" in
	let tranSet = Automata.tranMap_to_tranSet automata.tran in
 	let (q0,instr,q1) = TranSet.min_elt tranSet in
	let transitions = transitions^"["^"\""^(Core.Int.to_string q0)^"\""^","^"\""^(Char.escaped (InstrMap.find instr instr_char_map))^"\""^","^"\""^(Core.Int.to_string q1)^"\""^"]"  in 
	let tranSet = TranSet.remove (q0,instr,q1) tranSet in                   
	let transitions = TranSet.fold (fun (q0,instr,q1) transitions ->
		                                transitions^","^"["^"\""^(Core.Int.to_string q0)^"\""^","^"\""^(Char.escaped (InstrMap.find  instr instr_char_map))^"\""^","^"\""^(Core.Int.to_string q1)^"\""^"]"  ) tranSet transitions in
	let transitions = transitions^"\n],"^"\n" in
	
	(*接受状态转为json格式*)
	let receive = ref automata.receive in
	let acceptStates = "acceptStates : [" in
	let min_elt = NumSet.min_elt !receive in
	let acceptStates = acceptStates^"\""^(Core.Int.to_string min_elt)^"\"" in
	receive := NumSet.remove min_elt !receive;
	let acceptStates = NumSet.fold (fun q0 acceptStates ->  acceptStates^","^"\""^(Core.Int.to_string q0)^"\"" ) !receive  acceptStates in
	let acceptStates = acceptStates^"]\n" in
	
	let s = "{\n"^kind^description^name^(!alphabet)^state^initialState^transitions^acceptStates^"}" in
	
(*	Printf.printf "########################################### json  ##################################################";
	Printf.printf "%s\n" s;   *)
	(*---------------------------------------------------------------------------------------------*)
  (*调用OCamlFlat中的接口 此处为确定化*)
	let fa = new OCamlFlat.FiniteAutomaton.model (Text s) in		
  let mfa = match choose with
	          | 1 ->(* Printf.printf "%s\n"  "---------------toDeterministic-----------------------------"; *) fa#toDeterministic
						| 2 -> Printf.printf "%s\n"  "---------------minimize------------------------------------"; fa#minimize
						| 3 -> Printf.printf "%s\n"  "---------------cleanUselessStates--------------------------"; fa#cleanUselessStates
						| 4 -> Printf.printf "%s\n"  "---------------deter+min ----------------------------------"; let fa=fa#toDeterministic in fa#minimize
						| 5 -> Printf.printf "%s\n"  "---------------toJSon--------------------------------------"; fa
						| _ -> Printf.printf "%s\n"  "please choose 1、2、3、4 OR 5 ";assert false   in
		
(*	let j = mfa#toJSon in		
		OCamlFlatSupport.JSon.show j; *)
	(*---------------------------------------------------------------------------------------------*)


	(*将得到的结果转为需要的数据结构  StateNumMap *)
	let rep = mfa#representation in
	let num = ref (-1) in
	let state_num_map = List.fold_left (fun state_num_map s -> num := !num+1;
	                                                           StateNumMap.add s !num state_num_map ) StateNumMap.empty  (OCamlFlatSupport.Set.toList rep.allStates) in
	
	
  let start = StateNumMap.find rep.initialState state_num_map in
	let receive = List.fold_left (fun receive s -> NumSet.add  (StateNumMap.find s state_num_map )  receive ) NumSet.empty  (OCamlFlatSupport.Set.toList rep.acceptStates) in
	let tran_set = List.fold_left (fun tran_set (a,b,c) ->  
		                             TranSet.add ( (StateNumMap.find a state_num_map ),(CharInstrMap.find b char_instr_map) , (StateNumMap.find c state_num_map ) ) tran_set
				                                                                             )   TranSet.empty   (OCamlFlatSupport.Set.toList rep.transitions) in
	let tran = tranSet_to_tranMap tran_set in
	{start; receive; tran}
	
	
	
(*---------------------------------------------------------------- 自动机确定化 (两个确定的自动机并之后的确定化) ------------------------------------------------------------------------*)	

let rec automata_determin_auxi  automata state_set_temp state_num_map receive tran num =	
	  
	  let tran_old = !tran in
	(*	Printf.printf "determin\n";
		flush stdout; *)
	  let stateSet_new = StateSet.fold (fun num_set stateSet_new  ->
		          
								let num_that = StateSetNumMap.find num_set !state_num_map in	
                let coset_q0 = NumSet.fold (fun q0 coset_q0 ->
                    let coset0 = TranMap.find  q0 automata.tran in
										CoSet.union 	coset_q0 coset0;			
												  ) num_set CoSet.empty in
																				 			
								 let instr_accessed = ref (InstrSet.empty) in
								 let state_next = ref (NumSet.empty) in
								 let coset_num = ref (TranMap.find num_that !tran) in
								 CoSet.fold (fun (instr1,q1) stateSet_new ->
										
									   if not (InstrSet.mem  instr1 !instr_accessed )
										    then begin
													     instr_accessed := InstrSet.add instr1 !instr_accessed;	
															 let flag = ref false in											 
													     let next_state = CoSet.fold (fun (instr2,q2) next_state ->
														          if instr1=instr2
    																					   then begin
																									    if (NumSet.mem q2 automata.receive)
																											    then flag := true
																													else ()  ;
																									    NumSet.add q2 next_state
																										  end
    																						 else next_state
																			 ) coset_q0 NumSet.empty   in
				
													           let next_state_num = StateSetNumMap.find_opt  next_state !state_num_map in
															       match next_state_num with
																       | Some num0 ->  coset_num := CoSet.add (instr1,num0) !coset_num;
																			                 tran := TranMap.add num_that !coset_num !tran; 																			 							   
        											                         stateSet_new
                              												 
        												                       
																			 | None -> num := !num+1;
																				         state_num_map := StateSetNumMap.add  next_state !num !state_num_map;
																				         coset_num := CoSet.add (instr1,!num) !coset_num;
																			           tran := TranMap.add num_that !coset_num !tran; 
																								 tran := TranMap.add  (!num) CoSet.empty !tran;
																			           
																								 if !flag
                      																    then receive := NumSet.add !num !receive 
                      																		else ()   ; 
																								StateSet.add next_state stateSet_new
													    
													   end		
												else stateSet_new      ) coset_q0  stateSet_new              ) state_set_temp StateSet.empty in
 																				
		if 	(tran_old = !tran)		
		    then ()
				else automata_determin_auxi  automata stateSet_new state_num_map receive tran num 											
		
			
let automata_determin automata = 
	  if TranMap.is_empty automata.tran 
		   then  automata
			 else   begin
  				      let num = ref 0 in
            	  let state_set_temp = StateSet.add (NumSet.add automata.start NumSet.empty) StateSet.empty in
            		let state_num_map = ref (StateSetNumMap.add  (NumSet.add (automata.start) NumSet.empty)  !num  StateSetNumMap.empty) in
            		let tran = ref (TranMap.add !num CoSet.empty TranMap.empty) in
            		let receive = ref NumSet.empty in  
            		automata_determin_auxi  automata state_set_temp state_num_map receive tran num;
            		{start=0;receive=(!receive);tran=(!tran)}
							end

(*----------------------------------------------------------------------- 去除空串转移--------------------------------------------------------------------------------------*)		
(*获得空串传递闭包*)
let rec get_eq_set  q0 eq_set_old tran = 
	  let coset = TranMap.find q0 tran in
		CoSet.fold(fun (instr,q1) eq_set_new ->
			    if (instr = Execution.Skip) 
					   then  begin
							      let eq_set_temp = NumSet.add q1 eq_set_new in
										if(eq_set_temp = eq_set_new)
										   then  eq_set_temp
											 else  get_eq_set  q1 eq_set_temp tran										
									 end 
						 else  eq_set_new
				   ) coset  eq_set_old


let rec automata_remove_eplision_auxi  automata state_set_temp state_num_map tran receive num = 
    let tran_old = !tran in
		let stateSet_temp = StateSet.fold (fun num_set state_set_temp  ->
			   	let num_that = StateSetNumMap.find num_set !state_num_map in	
					
          let coset_q0 = NumSet.fold (fun q0 coset_q0 ->
                    let coset0 = TranMap.find  q0 automata.tran in
										CoSet.union 	coset_q0 coset0;			
												  ) num_set CoSet.empty in
													
					let coset_q0 = CoSet.fold (fun (instr,q1) coset ->
						                 if instr =  Execution.Skip
														    then coset
																else CoSet.add (instr,q1) coset  ) coset_q0 CoSet.empty in
					let coset_that = ref (TranMap.find num_that !tran) in
					
					CoSet.fold  (fun (instr,q1) state_set_temp ->
						       let next_state = get_eq_set  q1 (NumSet.add q1 NumSet.empty) automata.tran in
									 let flag = ref false in
									 NumSet.iter (fun q -> if (NumSet.mem q automata.receive)
									                          then  flag := true
																						else  ()          ) next_state;
									 let num_next =  StateSetNumMap.find_opt  next_state !state_num_map in
									 match num_next with
									   | Some num0 -> coset_that := CoSet.add (instr,num0) !coset_that;
											              tran := TranMap.add num_that !coset_that !tran; 																			 							   
        											      state_set_temp
											
										 | None -> num := !num+1; 	
											         state_num_map := StateSetNumMap.add  next_state !num !state_num_map;
											         coset_that := CoSet.add (instr,!num) !coset_that;
										           tran := TranMap.add num_that !coset_that !tran; 
															 tran := TranMap.add  (!num) CoSet.empty !tran;
															
															 if !flag
                      					   then receive := NumSet.add !num !receive 
                      						 else ()   ; 
															 StateSet.add next_state state_set_temp
									
							            )  coset_q0 state_set_temp
			
			         ) state_set_temp StateSet.empty in
			
				if 	(tran_old = !tran)		
		    then ()
				else automata_remove_eplision_auxi  automata stateSet_temp state_num_map tran receive num 
			
			

let automata_remove_eplision  automata = 
	  let num = ref 0 in
		let q0_eq_set = get_eq_set  automata.start (NumSet.add automata.start NumSet.empty) automata.tran in
		let state_set_temp = StateSet.add  q0_eq_set StateSet.empty in
		let state_num_map = ref (StateSetNumMap.add   q0_eq_set !num  StateSetNumMap.empty) in
		let tran = ref (TranMap.add !num CoSet.empty TranMap.empty) in
		let receive = ref NumSet.empty in  
		automata_remove_eplision_auxi   automata state_set_temp state_num_map tran receive num;
		{start=0;receive=(!receive);tran=(!tran)}
	
		
(*----------------------------------------------------------------------- 自动机的并 --------------------------------------------------------------------------------------*)

let automata_union automata1 automata2 instr_set = 
	 if (TranMap.is_empty automata1.tran) 
	    then  automata2
	 else if (TranMap.is_empty automata2.tran)
	    then  automata1
	 else   begin		 
		
		         
        	  let state_set1 = TranMap.fold (fun q0 coset state_set1 ->
        			                               NumSet.add q0 state_set1  ) automata1.tran NumSet.empty in
        	  let num = ref ( (NumSet.max_elt state_set1)+1 ) in
        		
        		let coset1 = TranMap.find automata1.start automata1.tran in
						
        	  let tran2 = TranMap.fold (fun q0 coset tran2 -> 
        			                            let coset_new  = CoSet.fold (fun (instr, q1) coset_new -> if q1=automata2.start
        																	                                                             then  CoSet.add (instr, automata1.start) coset_new
        																																															 else  CoSet.add (instr, q1+(!num) ) coset_new   ) coset CoSet.empty in
        																	if q0=automata2.start
        																	   then TranMap.add automata1.start coset_new tran2
        																		 else TranMap.add (q0+(!num)) coset_new tran2								) automata2.tran  TranMap.empty in 
        		
        		let coset2 = TranMap.find automata1.start tran2 in
        		let coset1 = CoSet.union coset1 coset2 in
        		let tran = TranMap.add automata1.start coset1 automata1.tran in
        		let tran2 = TranMap.remove automata1.start tran2 in
        		let tran = TranMap.fold (fun q0 coset tran ->
        			                            TranMap.add q0 coset tran ) tran2 tran in
        		let receive2 = NumSet.fold (fun q0 receive2 -> 
        			                              if q0=automata2.start
        																		   then NumSet.add automata1.start receive2
        																			 else NumSet.add (q0+(!num)) receive2  ) automata2.receive NumSet.empty in
        		let receive = NumSet.union automata1.receive receive2 in
						(*  automata_determin {start=automata1.start;receive;tran} *)
						
						{start=automata1.start;receive;tran} 
        		(*ocamlflat_utils {start=automata1.start;receive;tran} instr_set 1 *)
				 end
		
(*-------------------------------------------------------------------- 自动机的连接 --------------------------------------------------------------------------------------*)		

(*automata2连接到automata1之后*)
let automata_connect automata1 automata2 = 
	
	  let receive = ref NumSet.empty in
	  let state_set = ref (TranMap.fold (fun q0 coset state_set ->  NumSet.add q0 state_set ) automata1.tran NumSet.empty) in
		let num = ref (NumSet.max_elt !state_set + 1 ) in
		let tran = NumSet.fold (fun q_receive tran ->
                let tran2 = TranMap.fold (fun q0 coset tran2 -> 
                             let coset_new  = CoSet.fold (fun (instr, q1) coset_new -> if q1=automata2.start
      									                                                             then  CoSet.add (instr, q_receive ) coset_new
      																																							 else  CoSet.add (instr, q1+(!num) ) coset_new   ) coset CoSet.empty in
      												if q0=automata2.start
      												   then begin
																	     if (NumSet.mem q0 automata2.receive)
																			    then receive := NumSet.add q0 !receive
																					else ()
																			 ;
																	     TranMap.add q_receive coset_new tran2
																			end
      													 else 
																	    begin
																	    if (NumSet.mem q0 automata2.receive)
																			    then receive := NumSet.add (q0+(!num)) !receive
																					else ()
																			;
																			state_set := NumSet.add (q0+(!num)) !state_set; 
																	    TranMap.add (q0+(!num)) coset_new tran2			
																			end                                					) automata2.tran  TranMap.empty in 
									
								let coset1 = TranMap.find q_receive tran in							
      					let coset2 = TranMap.find q_receive tran2 in
            		let coset1 = CoSet.union coset1 coset2 in
            		let tran = TranMap.add q_receive coset1 tran in
								
            		let tran2 = TranMap.remove q_receive tran2 in
								num := (NumSet.max_elt !state_set + 1 );
            		TranMap.fold (fun q0 coset tran ->
            			                            TranMap.add q0 coset tran ) tran2 tran												
							) automata1.receive automata1.tran   in			
		{start=automata1.start; receive=(!receive); tran}
		


(*---------------------------------------------------------------- 自动机的交 ---------------------------------------------------------------------------------*)		

let rec product_generate pair_set_old receive automata1 automata2 tran state_set num  = 
	
	let tran_old = !tran in
	
(*	Printf.printf "product\n";
	Printf.printf "%d\n" !num ;
	flush stdout;  *)
	
	let pair_set = StatePairSet.fold (fun  (q0,q1) pair_set ->
		          
														let first_set = TranMap.find q0 automata1.tran in														
														let second_set = TranMap.find q1 automata2.tran in   
																												
                            let (key,state1,state2) = StateTripleSet.find (-1,q0,q1) !state_set in
														let coset = ref ( TranMap.find key !tran) in
							
					   (*对每一个旧的状态对  得到新的状态对*)							
					   let pair_set_new = CoSet.fold ( fun (instr1, q12) pair_set ->
  															 CoSet.fold (fun (instr2, q22)  pair_set  ->
  																   if instr1 = instr2 then
      																		begin    																																																																										
      																			let state_find = StateTripleSet.find_opt (-1,q12,q22) !state_set in
      																			match state_find with
      																			| None -> num := !num +1;
      																				        state_set := StateTripleSet.add (!num,q12,q22) !state_set;	
  																										coset := CoSet.add (instr1,!num)	!coset;																	
      																		            tran := TranMap.add !num CoSet.empty !tran;
																											
      																						  	if (NumSet.mem q12 automata1.receive ) && 
      																			             (NumSet.mem q22 automata2.receive )
      																		               then receive := NumSet.add !num !receive
      																			             else receive := !receive
      																			             ;
  																										StatePairSet.add (q12,q22)  pair_set
      																			| Some (key2,num11,num22) -> coset := CoSet.add (instr1, key2) !coset;
  																						                           pair_set
      																		end
  																	else pair_set
																) second_set  pair_set)  first_set pair_set   in
																
												tran := TranMap.add key !coset !tran;
												pair_set_new
																
									   ) pair_set_old   StatePairSet.empty in
	 	
		
	 if  (Automata.comp_tran_num tran_old = Automata.comp_tran_num !tran)  then                                                (* 判等这里希望库函数‘=’没错 *)
	     begin
				 if NumSet.is_empty  !receive
				    then {start = (-1); receive = NumSet.empty; tran = TranMap.empty}
						else {start = 0;receive = !receive; tran = !tran}		 
			 end
		
																						
	 else product_generate pair_set receive automata1 automata2 tran state_set num 

(*从接受状态向前获得所有可用节点*)	
let rec get_useable tran useable_state state_temp = 
(*	Printf.printf "??\n";
	flush stdout;  *)
	let useable_state_old = !useable_state in
	let state_temp_new = TranMap.fold (fun q0 coset state_temp_new -> 
		                                     let flag = ref false in
																				 CoSet.iter ( fun (instr, q1) -> if (NumSet.mem q1 state_temp)
																						                                    then flag := true
																																								else ()   ) coset  ;
																				 if !flag 
																					  then begin
																					       useable_state := NumSet.add q0 !useable_state;
																				         NumSet.add q0 state_temp_new
																						     end  
		                                        else state_temp_new
                                     ) tran  NumSet.empty in
																				
	if (NumSet.equal useable_state_old !useable_state ) then !useable_state
		                                  else get_useable  tran useable_state state_temp_new
	
	
(*-----------------------删除所有的无用节点 (*未考虑非连通的情况  不过只需判断初始节点是否在可用节点之中即可*)---------------------------*)	
let delete_useless_state tran_old receive = 
	 let useable_state = ref receive in
	 useable_state := get_useable tran_old  useable_state !useable_state;
	 flush stdout;
	 (*NumSet.iter (fun q0 -> Printf.printf "useable_state:%d\n" q0 )	 !useable_state;*)
	 TranMap.fold (fun q0 coset tran -> if (NumSet.mem q0 !useable_state)  
	                                               then begin 
																									      let coset = CoSet.fold (fun (instr, q1) coset ->
																													                        if (NumSet.mem q1 !useable_state )
																																									   then coset
																																										 else CoSet.remove (instr, q1) coset  ) coset coset  in
																												TranMap.add q0 coset tran
																								      end
																								 else TranMap.remove q0 tran ) tran_old tran_old
	


(*两个自动机求交   用一个状态对来记录当前两个自动机的位置*)
let automata_product automata1 automata2  = 
	if (TranMap.is_empty  automata1.tran  || TranMap.is_empty  automata2.tran )
	   then   {start = (-1);receive = NumSet.empty; tran = TranMap.empty}
		 else   begin
			         	let receive = ref NumSet.empty in
              (*	Printf.printf "product start+++\n";  *)
              	let num = ref 0 in
              	let start1 = automata1.start in
              	let start2 = automata2.start in
              	let start = StatePairSet.add (start1, start2)  StatePairSet.empty in
              	let state_set = ref (StateTripleSet.add (!num,start1, start2)  StateTripleSet.empty) in
              	
              	let tran = ref (TranMap.add !num CoSet.empty TranMap.empty) in
              	let product_result = product_generate start receive automata1 automata2 tran state_set num in	
              	let tran = delete_useless_state product_result.tran !receive  in
               (*  Printf.printf "product end+++\n";  
              	flush stdout;  *)
              	{product_result with tran=tran}	   
			      end

	
(*---------------------------------------------------------------- 自动机求补 ------------------------------------------------------------------------*)																																																																																																																																																																																				
(*获取一个状态的后继转移*)
let get_instr q tran =
		let coset = TranMap.find q tran in
		CoSet.fold (fun (instr,q1) instrSet  ->  InstrSet.add instr instrSet ) coset InstrSet.empty						
	
																	
																																	
(*对自动机求补  保存结果为 automata 类型的*)					(*对泛化结果*)				
let comp_automata  automata	 instr_set  = 		
	  let tran = ref automata.tran in			
		
	  (*获取所有状态*)
	  let state_set = ref (TranMap.fold (fun q0 coset state_set -> NumSet.add q0 state_set ) automata.tran NumSet.empty) 	in
		let num = ref (NumSet.max_elt !state_set +1) in
		
		TranMap.iter ( fun q0 coset -> 
        			             let instr_q = get_instr q0 !tran in
                           let add_instr = InstrSet.diff instr_set instr_q in 
          								 let coset = InstrSet.fold ( fun instr coset->CoSet.add (instr, !num) coset )  add_instr coset in
          								     tran := TranMap.add q0 coset !tran;
          					       let coset = InstrSet.fold(fun instr  coset ->  CoSet.add (instr, !num) coset )instr_set CoSet.empty in
          					           tran := TranMap.add !num coset !tran;
															 state_set := NumSet.add !num !state_set; 
          					           num := !num+1
													     
				          ) !tran
								  ;
		let receive = NumSet.diff !state_set automata.receive in
																	
	 {start=automata.start; receive; tran= (!tran)}		
	
	
	
(*----------------------------------------------------------------抽取一条程序路径----------------------------------------------------------------*)

(* 获取一个节点的所有后继节点   在判断有无循环时使用*)																											
let rec get_succ_auxi num tran succ_set_old = 
      let coset = TranMap.find num tran in
	    let num_temp = CoSet.fold (fun (instr, q1) num_temp -> NumSet.add q1 num_temp ) coset NumSet.empty in
	    let succ_set = NumSet.union num_temp succ_set_old in
	    if (succ_set = succ_set_old) 
	       then succ_set
	       else NumSet.fold (fun q0 succ_set -> let succ_q0 = get_succ_auxi q0 tran succ_set 
	                                                      in NumSet.union succ_set succ_q0) num_temp succ_set 
																												
let get_succ num tran = 
	  get_succ_auxi num tran NumSet.empty		


(*抽取一条程序路径*)
let rec get_exec automata execution q0 num = 
		let num = num + 1 in
		(*if num > 500
		   then [||]
			 else *) let coset = TranMap.find q0 automata.tran in
        		   if (NumSet.mem q0 automata.receive)
        		        then   execution
        			      else   let cadidate_array = CoSet.fold (fun (instr,q1) cadidate_array -> 
        				                                  Array.append  cadidate_array [|(instr,q1)|]  ) coset [||]   in
              						 let len = Array.length cadidate_array in 			
              						 let i = Random.int (Array.length cadidate_array) in
              			       let (instr,q1) = cadidate_array.(i)  in
              					   let execution = Array.append execution [|instr|] in
              					   get_exec automata execution q1 num 


(*从程序中抽取一条路径*)
let  get_execution automata = 
    	Random.init (int_of_float (Unix.gettimeofday ()));
    	(*get_exec automata [||] automata.start 0*)
    	(* tranMap_visualize	automata.tran;  
    	 flush stdout;  *)
    	let num = 0 in
    	let execution = ref (get_exec automata [||] automata.start num ) in
    	while (Array.length !execution = 0) do
    		let num = 0 in
    		execution := get_exec automata [||] automata.start num
       done;
    	!execution

(*
let rec get_exec automata execution q0 num = 
		let num = num + 1 in
		(*if num > 500
		   then [||]
			 else *) let coset = TranMap.find q0 automata.tran in
        		   if (NumSet.mem q0 automata.receive)
        		        then   execution
        			      else   let cadidate_array = CoSet.fold (fun (instr,q1) cadidate_array -> 
        				                                  Array.append  cadidate_array [|(instr,q1)|]  ) coset [||]   in
              						 let len = Array.length cadidate_array in 	
													 let q = ref (-1) in
													 let instr = ref Execution.Skip in
													 Array.iter (fun (instr_temp,q1) ->
														               let succ_set = get_succ q1 automata.tran in
																					 if not (NumSet.mem  q1 succ_set)
																					    then  begin 
																								      q := q1;
																											instr := instr_temp
																							      end
														               )  cadidate_array;	
																									
													 if !q = (-1)
													    then begin 
																     let i = Random.int (Array.length cadidate_array) in
																		 let (instr,q1) = cadidate_array.(i)  in
              					             let execution = Array.append execution [|instr|] in
              					             get_exec automata execution q1 num  
																	 end	
															else begin 
																     let execution = Array.append execution [|!instr|] in
              					             get_exec automata execution !q num  	
																	 end
              																													
																																									
(*从程序中抽取一条路径*)
let  get_execution automata = 
    	Random.init (int_of_float (Unix.gettimeofday ()));
    	(*get_exec automata [||] automata.start 0*)
    	(* tranMap_visualize	automata.tran;  
    	 flush stdout;  *)
    	let num = 0 in
    	let execution = ref (get_exec automata [||] automata.start num ) in
    	while (Array.length !execution = 0) do
    		let num = 0 in
    		execution := get_exec automata [||] automata.start num
       done;
    	!execution												
										*)
													
(*----------------------------------------------------------------- 判断一个自动机是否是另一个自动机的子集 --------------------------------------------------------------------------------------*)		
(*automata1（DFA） 是否是 automata2（NFA） 的子集  是的话返回空集  不是的话，返回一条反例路径*)

let rec is_contain_auxi  state1 state_set_2 pair_set execution automata1 automata2 = 
	      let flag = ref false in
			  NumSet.iter (fun state -> 
							             if NumSet.mem state automata2.receive
													    then  flag := true ) state_set_2;
        if (!flag && NumSet.mem state1 automata1.receive)
				   then  (true,[||])
				else if( not !flag &&  NumSet.mem state1 automata1.receive)  
						then  (false,execution)
						else  begin  let coset1 = TranMap.find state1 automata1.tran in
					               let is_contain = ref true in
												 let execution_res = ref [||] in
						             CoSet.iter ( fun (instr1, q11)  ->		 	
													if !is_contain
													   then begin
															     (* Printf.printf "%s\n" (Execution.string_of_instr instr1);  *)
															      let state_set_temp = ref NumSet.empty in																		
						                        let pair_set_temp = NumSet.fold (fun state pair_set ->
              													                       let coset2 = TranMap.find state automata2.tran in
              																								 CoSet.fold(fun (instr2,q22) pair_set ->
              																									           if  instr1 = instr2
              																														     then  begin																														       
              																																	      state_set_temp := NumSet.add q22 !state_set_temp;
              																																				StatePairSet.add (q11,q22) pair_set  
              																																		   end  
																																							 else  pair_set  
																																    ) coset2  pair_set
													                               ) state_set_2  pair_set   in  																														
													 
													         (*   Printf.printf "%s\n" "********************";
																			StatePairSet.iter (fun (q1,q2) ->
																				       Printf.printf "(%d," q1;
																							 Printf.printf "%d)\n"  q2;      ) pair_set_temp;  *)
													            
																			
 																		  let execution = Array.append execution [|instr1|] in		
																											
                                      if (NumSet.is_empty !state_set_temp)
				                                 then  begin
					                                      is_contain := false;
										                            execution_res := get_exec   automata1 execution q11 0
												                       end
      									                 else  begin 
																		           if (StatePairSet.cardinal pair_set = StatePairSet.cardinal pair_set_temp)              (*出现已经出现过的状态对，并不意味着循环    所以循环要怎么处理：每个分支保存其独立的状态对，若有重复出现的状态对，一定就是循环了*)
									                                 then  execution_res := [||]
										                               else  begin 
            															                let (flag_temp,execution_temp) = is_contain_auxi  q11 !state_set_temp pair_set_temp execution automata1 automata2 in
            																							is_contain := flag_temp;
            																							execution_res := execution_temp
													                                end 
													                     end											            
																	end			  		
															else () 		 ) coset1; 			
													(!is_contain,!execution_res)																					    											                
                   end


let  is_contain  automata1 automata2 =  
	   if (TranMap.is_empty  automata2.tran )
		    then assert false
			;	
	   if (TranMap.is_empty  automata1.tran )
	   then   [||]
		 else   begin								
								let start1 = automata1.start in
								let state_set_2 = NumSet.add automata2.start NumSet.empty in
								let pair_set =  StatePairSet.add (start1, automata2.start)  StatePairSet.empty in						
								let execution = [||] in			
							  let (is_contain,execution) =	is_contain_auxi   start1 state_set_2 pair_set execution automata1 automata2		in
								execution							
			      end
		
		

