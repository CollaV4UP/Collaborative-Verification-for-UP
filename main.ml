open Automata
(*---------------------------------------- 前端处理部分 ---------------------------------------------*)

module StringSet = Set.Make(
  struct
    type t = string
    let compare  = Stdlib.compare        	
  end)

(*---------------------------------------------------------------------------------------------*)
(*choose : 0 生成200个程序   1 累加复用的方式  2 原始程序复用的方式  3 分别复用*)
(* flag : true表示重用之前结果  false表示没有重用   *)

let main  choose file_address =
	 (*  Benchmark_generate.benchmark1_generate (); *)
   (*  Benchmark_generate.gen_block ()  *)
   (*  Benchmark_generate.benchmark_generate() ;  *) 
   (*  Benchmark_generate.stmt_mutation1 ();  *)
   (*  Benchmark_generate.stmt_mutation2 ();  *)
	Random.init (int_of_float (Unix.gettimeofday ()) );
	if choose = 0
	   then begin	    	
			      (* for i = 0 to 49 do
			            Benchmark_generate.bpl_to_unit  ("/home/dyd/project/github/BigAutomata/benchmark_fm/benchmark_bpl/benchmark"^(Core.Int.to_string i)^".bpl" ) 
						 done  *)
						Benchmark_generate.bpl_to_unit file_address;
			   (*  Benchmark_generate.block_mutation1();  *)
			     (*  Benchmark_generate.block_mutation_temp();   *)
			   (*   Benchmark_generate.random_programs () ;  *)
			   (*  Benchmark_generate.block_mutation ();  *)
					(*   Benchmark_generate.block_mutation ();
							for i = 0 to 499 do
				         Benchmark_generate.unit_to_bpl  ("./benchmark_combin/benchmark"^(Core.Int.to_string i)^".unit")
			        done;   *)
						
					 (* Benchmark_generate.stmt_mutation  file_address  *)
			    end
			;		
			
(*	
	if choose=0 
	   then begin
			        let time_start = Unix.gettimeofday () in 
              Benchmark_generate.stmt_mutation file_address; 
		          let time_end = Unix.gettimeofday () in 
		          Printf.printf "total_time:%f\n" (time_end -. time_start)    			   
			    end
	   ;
*)

	 (*获得所有程序的正则表达式:rgx_list (引用类型)   以及变量名:var_list    函数名:fun_list*)
		let rgx_arr = ref [||] in
		let prog_arr = ref [||] in
		let env_arr = ref [||] in
		let var_set = ref StringSet.empty in
		let fun_set = ref StringSet.empty in
			
		let pro_add_temp = String.sub  file_address 0 (String.length file_address - 6) in
		for i = 0 to 49 do
			  let var_list,fun_list,prog,env = Verification.parse_from_file (pro_add_temp ^(Core.Int.to_string i)  ^".unit" ) in  
  		(*	let var_list,fun_list,prog,env = parse_from_file ("./record/test" ^ (Core.Int.to_string i) ^ ".unit" ) in  *)
	  	(*	let var_list,fun_list,prog,env = Verification.parse_from_file ("./benchmark1/benchmark" ^ (Core.Int.to_string i) ^ ".unit" ) in  *)
			(*  let var_list,fun_list,prog,env = parse_from_file ("./benchmark_mutation/benchmark" ^ (Core.Int.to_string i) ^ ".unit" ) in  *)
  			let rgx = Execution.regexOfProg env prog in
			(*	Printf.printf "%s\n" (Execution.string_of_regex  rgx);  *)
  			List.iter(fun var  -> var_set := StringSet.add var !var_set) var_list;
  			List.iter(fun func -> fun_set := StringSet.add func  !fun_set) fun_list;
  			rgx_arr := Array.append  !rgx_arr [|rgx|]
		done;
		
		let var_list = StringSet.fold (fun var var_list -> List.append [var] var_list) !var_set [] in
		let fun_list = StringSet.fold (fun func fun_list -> List.append [func] fun_list) !fun_set [] in
				
		(*获得大自动机字母表*)
		let instr_set = Array.fold_left (fun instr_set rgx -> let instr_temp = Automata.get_instr rgx in
		                                Automata.InstrSet.union  instr_set  instr_temp ) Automata.InstrSet.empty !rgx_arr in
		
		let instr_set = Automata.InstrSet.remove Execution.Skip instr_set in										
																
		Printf.printf "vars:%d\n"  (List.length var_list);
		Printf.printf "funs:%d\n"  (List.length fun_list);
		Printf.printf "instrs:%d\n"  (Automata.InstrSet.cardinal instr_set);
		
		flush stdout;
								
(*-----------------------------------------------------------------------------------------------------------------------------------*)															
																									
(*得到程序自动机*)												
	    let automata_pro_ary =	Array.fold_left (fun pro_automata_ary rgx_pro ->			                                          
                                       let automata_pro = Automata.pro_automata rgx_pro in	
																			 let instr_temp = Automata.get_instr rgx_pro in
																			 let instr_temp = Automata.InstrSet.remove Execution.Skip instr_temp in
																			(* Printf.printf "%s\n" "---------------- pro_automata ---------------------------";
																			 tranMap_visualize	automata_pro.tran;  
																			 Printf.printf "--------------------------------------------------------------------\n";   *)
																			(* let automata_pro_test =  Automata_utils.automata_remove_eplision   automata_pro in  *)
																		  (* tranMap_visualize	automata_pro_test.tran;  
																			 NumSet.iter (fun q -> Printf.printf "receive:%d\n" q ) automata_pro_test.receive;	 *)																				
																	  	 let automata_pro =  Automata_utils.ocamlflat_utils automata_pro instr_temp 1 in 																			
																			(* let automata_pro = Automata_utils.automata_remove_eplision   automata_pro in		*)																										       																															
																			 Array.append pro_automata_ary [|automata_pro|]   ) [||] !rgx_arr in				                                             		
    		flush stdout;					


(*-----------------------------------------------------------------------------------------------------------------------------------*)		
(*flag = false 不复用   true 求并确定化方式的复用*)			
		if choose = 1
		    then begin				 					           			
                  let time_start = Unix.gettimeofday () in 			          
                 	let coll_automata = ref {start=0; receive = NumSet.empty; tran = TranMap.empty} in 
              		
              		let product_time = ref 0.0 in
              		let union_time = ref 0.0 in
									let ref_num_total = ref 0 in
                	(*tranMap_visualize	!coll_automata.tran; *)
                	flush stdout;						
                				 Array.iteri (fun i automata_pro ->
                					  (*对每一个程序执行下列流程*)
                						let pro_time_start = Unix.gettimeofday () in							
              							
              						(*	let instr_set = Automata.get_instr !rgx_arr.(i) in                                   (*此处设置不相关的语句仅是该程序的不相关语句*)
              							let instr_set = Automata.InstrSet.remove Execution.Skip instr_set in  *)
              							
                					  let is_correct = ref 0 in
                						let automata_pro = ref automata_pro  in 
                						let ref_num = ref 0 in  
                					  let coll_automata_temp = ref {start=0; receive = NumSet.empty; tran = TranMap.empty}  in     
                					  let union_time_stmt = ref 0.0 in
              							
                				(*		Printf.printf "------------------------- program automata ---------------------\n";
                						Automata.tranMap_visualize !automata_pro.tran;
                						Printf.printf "start:%d\n" !automata_pro.start;
                						NumSet.iter (fun q0 -> Printf.printf "receive:%d\n" q0 ) !automata_pro.receive;
                						Printf.printf "----------------------------------------------------------------\n";  *)
                						
              							Printf.printf "--------------------------------------------demo%i---------------------------------------------------\n"  i;
                						while not (TranMap.is_empty !automata_pro.tran) && !is_correct=0 do
              								  let time_now = Unix.gettimeofday () in
              								(*	Printf.printf "states：%d\n"  (Automata.TranMap.cardinal !automata_pro.tran);  *)
              									
              											 if ( int_of_float (time_now -. pro_time_start) )> 200
              											    then  is_correct := 2
              													else  begin													
                              										 if (TranMap.is_empty  !automata_pro.tran)
                              										   then ()
                              											 else  begin
                              													       (*抽取路径*)
                              															(*	 Printf.printf "refindment %d: --------------------------------------------------------------------------------------\n " !ref_num ;   		
        																											 flush stdout;		*)							
                              												         let execution = Automata_utils.get_execution !automata_pro in	 
                            																	
                            																	
                              															 (*	 Printf.printf "----------- 取到的路径 -------------\n";
                              																 Array.iteri (fun i instr -> Printf.printf "%d--" i; Printf.printf "%s\n" (Execution.string_of_instr instr) ) execution;  
                                                               flush stdout;  *)   
                              																														 
                              																 (*判断是否为真反例*)
                              																 let is_feasible = Coherence.is_feasible execution var_list fun_list in
                              																  if is_feasible = 0
                              			                                 then begin is_correct := 1; Array.iter (fun instr -> Printf.printf "%s\n" (Execution.string_of_instr instr) ) execution    end  
                              					                             else begin 	 																								    																		 
                              																				    (*对假反例泛化*)
                              																				    let (gen_automata,_class) = Refinement.gen_automata  execution var_list fun_list instr_set is_feasible  in																																																								
                              																						let gen_automata = Automata_utils.automata_determin  gen_automata in
        																																(*	Printf.printf "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n"; 
        																																	flush stdout;		*)
                            																							
                            																					 (* 	Printf.printf "---------------- 泛化得到的自动机为: -------------------\n";
                            																							Automata.tranMap_visualize gen_automata.tran;    
        																																	NumSet.iter (fun q0 -> Printf.printf "receive:%d\n" q0 ) gen_automata.receive;  *)
                            																																																							
        																																	
                              																					(*	Printf.printf "&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n";  
        																																	flush stdout;		*)
                              																						(*取反*)
                              																					  let comp_automata = Automata_utils.comp_automata  gen_automata instr_set in			
        																																	
        																																(*	Printf.printf "comp*********************************************************\n";  
        																																	flush stdout;		*)
        																																																		
                              																				    automata_pro := Automata_utils.automata_product  !automata_pro comp_automata;  
        																																	
        																																(*	Printf.printf "product*********************************************************\n";  
        																																	flush stdout;		*)
                              																						ref_num := !ref_num+1;       
                              																						end
                                                              end   
              															 end  
                                    	done;																 
                																		
              										let union_start = Unix.gettimeofday () in	
              										
              									 
              									  let union_end = Unix.gettimeofday () in	
              										Printf.printf "union_time: %f\n"  (union_end -. union_start +. !union_time_stmt) ;
              										union_time := ( !union_time +. (union_end -. union_start) +. !union_time_stmt); 
              										
              									  let pro_time_end = Unix.gettimeofday () in									
              										flush stdout;
              										
                									Printf.printf "refindment nums:%d\n" !ref_num ;															
              										ref_num_total := !ref_num_total + !ref_num;																																				  								
                								  if !is_correct = 0
                									   then begin 
                											       Printf.printf "verify_time: %f\n"  (pro_time_end-.pro_time_start);
                											       Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "correct";
              															 Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)
                										      end
                								  else  if !is_correct = 1
              										       then  begin 
                      											      Printf.printf "verify_time: %f\n"  (pro_time_end-.pro_time_start);
                      											      Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "incorrect";
              																		Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)	
                												       end		
              										else  begin
              											     Printf.printf "verify_time: %f\n"  (pro_time_end-.pro_time_start);
                      									 Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "time_out";
              													 Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)	
              											    end
              										;
              										
              										Printf.printf "union_time百分比:%f\n"  ( (union_end -. union_start) /. (pro_time_end-.pro_time_start) );
              										
              										if(i=9) || (i=19) || (i=39) || (i=59) || (i=79) || (i=99) || (i=199) || (i=299) || (i=399) || (i=499) || (i=599)	|| (i=699) || (i=799) || (i=899) || (i=999)
              									   then  begin  
              											       Printf.printf "----------------------------------------前%d个---------------------------------------\n"  (i+1);
              														 Printf.printf "time_cost:%f\n"  (pro_time_end-.time_start);
              														 Printf.printf "product_time:%f\n"  !product_time;
              														 Printf.printf "product_time百分比:%f\n"  ( !product_time /. (pro_time_end-.time_start));
              						                 Printf.printf "union_time:%f\n"  !union_time;
              														 Printf.printf "union_time百分比:%f\n"  ( !union_time /. (pro_time_end-.time_start));
              
              										       end
              									   else ()							
                								;																		
                								 ) automata_pro_ary;								 
                				  let time_end = 	Unix.gettimeofday () in 
              						Printf.printf "###########################################################################################";
                					Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran);
													Printf.printf "refin_nums_total:%d\n" !ref_num_total;
                					Printf.printf "runtime:%f\n"  (time_end-.time_start);																													
                          Printf.printf "product_time:%f\n"  !product_time;
              						Printf.printf "union_time:%f\n"  !union_time;
              						Printf.printf "product_time百分比:%f\n"  ( !product_time /. (time_end-.time_start) );
                          Printf.printf "union_time百分比:%f\n"  ( !union_time /. (time_end-.time_start) );
             end
           ;

(*  用第一个程序对其他程序做复用  *)
(*-----------------------------------------------------------------------------------------------------------------------------------*)					
	if choose = 2
	   then begin											        			
                  let time_start = Unix.gettimeofday () in 			          
                 	let coll_automata = ref {start=0; receive = NumSet.empty; tran = TranMap.empty} in 
              		let product_time = ref 0.0 in
									let ref_num_total = ref 0 in
                	(*tranMap_visualize	!coll_automata.tran; *)
                	flush stdout;						
                				 Array.iteri (fun i automata_pro ->
                					  (*对每一个程序执行下列流程*)
                						let pro_time_start = Unix.gettimeofday () in							
              							
              							let instr_set = Automata.get_instr !rgx_arr.(i) in
              							let instr_set = Automata.InstrSet.remove Execution.Skip instr_set in
              							
                					  let is_correct = ref 0 in
                						let automata_pro = ref automata_pro  in 
              							let automata_pro_temp = !automata_pro in
                						let ref_num = ref 0 in       
                					
                				(*		Printf.printf "------------------------- program automata ---------------------\n";
                						Automata.tranMap_visualize !automata_pro.tran;
                						Printf.printf "start:%d\n" !automata_pro.start;
                						NumSet.iter (fun q0 -> Printf.printf "receive:%d\n" q0 ) !automata_pro.receive;
                						Printf.printf "----------------------------------------------------------------\n";  *)
                						Printf.printf "--------------------------------------------demo%i---------------------------------------------------\n"  i;	
              								
                						while not (TranMap.is_empty !automata_pro.tran) && !is_correct=0 do
              								  let time_now = Unix.gettimeofday () in
              								(*	Printf.printf "states：%d\n"  (Automata.TranMap.cardinal !automata_pro.tran);  *)
              									
              											 if ( int_of_float (time_now -. pro_time_start) )> 500
              											    then  is_correct := 2
              													else  begin								
                                    						        (*先对求交验证*)																				
                                    										 if not (TranMap.is_empty !coll_automata.tran) && !ref_num = 0
                                    										    then begin 																									
              																										let product_start = Unix.gettimeofday () in					
              																																					
                                    													    let comp_automata = Automata_utils.comp_automata !coll_automata instr_set in																					
                                    													    automata_pro := Automata_utils.automata_product !automata_pro comp_automata; 	
              																										
              																																						
              																										let product_end = Unix.gettimeofday () in	
              																					         	Printf.printf "product_time: %f\n"  (product_end -. product_start);																							
              																						        product_time := ( !product_time +. (product_end -. product_start) );
              																									 end
                                    												else ()
                                    											;
                                    										
                                    										 if (TranMap.is_empty  !automata_pro.tran)
                                    										   then ()
                                    											 else  begin
                                    													       (*抽取路径*)
                                    															(*	 Printf.printf "refindment %d: --------------------------------------------------------------------------------------\n " !ref_num ;   		
              																											 flush stdout;		*)							
                                    												         let execution = Automata_utils.get_execution !automata_pro in	 
                                  																	
                                  																	
                                    															 (*	 Printf.printf "----------- 取到的路径 -------------\n";
                                    																 Array.iteri (fun i instr -> Printf.printf "%d--" i; Printf.printf "%s\n" (Execution.string_of_instr instr) ) execution;  
                                                                     flush stdout;   *)
                                    																														 
                                    																 (*判断是否为真反例*)
                                    																 let is_feasible = Coherence.is_feasible execution var_list fun_list in
                                    																 if is_feasible = 0
                                    			                                 then begin is_correct := 1; Array.iter (fun instr -> Printf.printf "%s\n" (Execution.string_of_instr instr) ) execution    end  
                                    					                             else begin 	 																								    																		 
                                    																				    (*对假反例泛化*)
                                    																				    let (gen_automata,_class) = Refinement.gen_automata  execution var_list fun_list instr_set is_feasible  in																																																								
                                    																						let gen_automata = Automata_utils.automata_determin  gen_automata in
              																																(*	Printf.printf "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n"; 
              																																	flush stdout;		*)
                                  																							
                                  																					(*		Printf.printf "---------------- 泛化得到的自动机为: -------------------\n";
                                  																							Automata.tranMap_visualize gen_automata.tran;    
              																																	NumSet.iter (fun q0 -> Printf.printf "receive:%d\n" q0 ) gen_automata.receive;  *)
                                  																							
              																																	
                                    																					(*	Printf.printf "&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n";  
              																																	flush stdout;		*)
                                    																						(*取反*)
                                    																					  let comp_automata = Automata_utils.comp_automata gen_automata instr_set in			
              																																	
              																																(*	Printf.printf "comp*********************************************************\n";  
              																																	flush stdout;		*)
              																																																		
                                    																				    automata_pro := Automata_utils.automata_product !automata_pro comp_automata;  
              																																	
              																																(*	Printf.printf "product*********************************************************\n";  
              																																	flush stdout;		*)
                                    																						ref_num := !ref_num+1;       
                                    																						end
                                                                    end   
              															 end  
                                    	done;																 
                									let pro_time_end = Unix.gettimeofday () in
              									 
                									Printf.printf "refindment nums:%d\n" !ref_num ;															
              										ref_num_total := !ref_num_total + !ref_num;		
																																																					  								
                								  if !is_correct = 0
                									   then begin 
              												    if (i = 0)
              														   then coll_automata := automata_pro_temp
              												       else ()
              															 ;
                											       Printf.printf "verify_time: %f\n"  (pro_time_end-.pro_time_start);
                											       Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "correct";
              															 Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)
                										      end
                								  else  if !is_correct = 1
              										       then  begin 
                      											      Printf.printf "verify_time: %f\n"  (pro_time_end-.pro_time_start);
                      											      Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "incorrect";
              																		Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)	
                												       end		
              										else  begin
              											     Printf.printf "verify_time: %f\n"  (pro_time_end-.pro_time_start);
                      									 Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "time_out";
              													 Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)	
              											    end
              										;
              										
              										if(i=9) || (i=19) || (i=39) || (i=59) || (i=79) || (i=99) || (i=199) || (i=299) || (i=399) || (i=499) || (i=599)	|| (i=699) || (i=799) || (i=899) || (i=999)
              									   then  begin  
              											       Printf.printf "----------------------------------------前%d个---------------------------------------\n"  (i+1);
              														 Printf.printf "time_cost:%f\n"  (pro_time_end-.time_start);
              														 Printf.printf "product_time:%f\n"  !product_time;
              														 Printf.printf "product_time百分比:%f\n"  ( !product_time /. (pro_time_end-.time_start) );
              										       end
              									   else ()							
                								;																		
                								 ) automata_pro_ary;								 
                				  let time_end = 	Unix.gettimeofday () in 
              						Printf.printf "###########################################################################################";
                					Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran);
													Printf.printf "refin_nums_total:%d\n" !ref_num_total;
                					Printf.printf "runtime:%f\n"  (time_end-.time_start);	
                          Printf.printf "product_time:%f\n"  !product_time;
              						Printf.printf "product_time百分比:%f\n"  ( !product_time /. (time_end-.time_start) )
             end
             ;
						
(* 累加变异场景下  前一个程序（若为正确）对后一个验证 *)
(*-----------------------------------------------------------------------------------------------------------------------------------*)								
		if choose = 3
		   then  begin											
                  			
                      let time_start = Unix.gettimeofday () in 			          
                     	let coll_automata = ref {start=0; receive = NumSet.empty; tran = TranMap.empty} in 
											let ref_num_total = ref 0 in
                    	(*tranMap_visualize	!coll_automata.tran; *)
                    	flush stdout;						
                    				 Array.iteri (fun i automata_pro ->
                    					  (*对每一个程序执行下列流程*)
                    						let pro_time_start = Unix.gettimeofday () in							
                  							
                  							let instr_set = Automata.get_instr !rgx_arr.(i) in
                  							let instr_set = Automata.InstrSet.remove Execution.Skip instr_set in
                  							
                    					  let is_correct = ref 0 in
                    						let automata_pro = ref automata_pro  in 
                  							let automata_pro_temp = !automata_pro in
                    						let ref_num = ref 0 in  
                    					  let coll_automata_temp = ref {start=0; receive = NumSet.empty; tran = TranMap.empty}  in     
                    					
                    				(*		Printf.printf "------------------------- program automata ---------------------\n";
                    						Automata.tranMap_visualize !automata_pro.tran;
                    						Printf.printf "start:%d\n" !automata_pro.start;
                    						NumSet.iter (fun q0 -> Printf.printf "receive:%d\n" q0 ) !automata_pro.receive;
                    						Printf.printf "----------------------------------------------------------------\n";  *)
                    							
                    						while not (TranMap.is_empty !automata_pro.tran) && !is_correct=0 do
                  								  let time_now = Unix.gettimeofday () in
                  								(*	Printf.printf "states：%d\n"  (Automata.TranMap.cardinal !automata_pro.tran);  *)
                  									
                  											 if ( int_of_float (time_now -. pro_time_start) )> 500
                  											    then  is_correct := 2
                  													else  begin								
                              						        (*先对求交验证*)																				
                              										 if not (TranMap.is_empty !coll_automata.tran) && !ref_num = 0
                              										    then begin 
                              													    let comp_automata = Automata_utils.comp_automata !coll_automata instr_set in																					
                              													    automata_pro := Automata_utils.automata_product !automata_pro comp_automata; 
        																									  coll_automata := {start=0; receive = NumSet.empty; tran = TranMap.empty}             																										   
                              														 end
                              												else ()
                              											;
                              										
                              										 if (TranMap.is_empty  !automata_pro.tran)
                              										   then ()
                              											 else  begin
                              													       (*抽取路径*)
                              																(* Printf.printf "refindment %d: --------------------------------------------------------------------------------------\n " !ref_num ;   		
        																											 flush stdout;			*)						
                              												         let execution = Automata_utils.get_execution !automata_pro in	 
                            																	
                            																	
                              															 (*	 Printf.printf "----------- 取到的路径 -------------\n";
                              																 Array.iteri (fun i instr -> Printf.printf "%d--" i; Printf.printf "%s\n" (Execution.string_of_instr instr) ) execution;  
                                                               flush stdout;   *)
                              																														 
                              																 (*判断是否为真反例*)
                              																 let is_feasible = Coherence.is_feasible  execution var_list fun_list in
                              																 if is_feasible = 0
                              			                                 then begin is_correct := 1; Array.iter (fun instr -> Printf.printf "%s\n" (Execution.string_of_instr instr) ) execution    end  
                              					                             else begin 	 																								    																		 
                              																				    (*对假反例泛化*)
                              																				    let (gen_automata,_class) = Refinement.gen_automata  execution var_list fun_list instr_set is_feasible in																																																								
                              																						let gen_automata = Automata_utils.automata_determin  gen_automata in
        																																(*	Printf.printf "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n"; 
        																																	flush stdout;		*)
                            																							
                            																						(*	Printf.printf "---------------- 泛化得到的自动机为: -------------------\n";
                            																							Automata.tranMap_visualize gen_automata.tran;    
        																																	NumSet.iter (fun q0 -> Printf.printf "receive:%d\n" q0 ) gen_automata.receive;  *)
                            																							
                              																					(*	if flag && not (i = Array.length automata_pro_ary-1) (* && (_class != 4 ) *)
                              																						   then  coll_automata_temp := Automata_utils.automata_union  gen_automata !coll_automata_temp instr_set																							       
                              																							 else  ()
                              																						;   *)
        																																	
                              																					(*	Printf.printf "&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n";  
        																																	flush stdout;		*)
                              																						(*取反*)
                              																					  let comp_automata = Automata_utils.comp_automata gen_automata instr_set in			
        																																	
        																																(*	Printf.printf "comp*********************************************************\n";  
        																																	flush stdout;		*)
        																																																		
                              																				    automata_pro := Automata_utils.automata_product !automata_pro comp_automata;  
        																																	
        																																(*	Printf.printf "product*********************************************************\n";  
        																																	flush stdout;		*)
                              																						ref_num := !ref_num+1;       
                              																						end
                                                              end   
                  													         end
                                        	done;																 
                    									let pro_time_end = Unix.gettimeofday () in
                    									Printf.printf "--------------------------------------------demo%i---------------------------------------------------\n"  i;
                  										flush stdout;
                  									 
                    									Printf.printf "refindment nums:%d\n" !ref_num ;															
                  										ref_num_total := !ref_num_total + !ref_num;	
																																																							  								
                    								  if !is_correct = 0                  									  
            														   then  begin
  																						     coll_automata := Automata_utils.automata_union  !coll_automata automata_pro_temp instr_set;       												       
                											             Printf.printf "verify_time: %f\n"  (pro_time_end-.pro_time_start);
                											             Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "correct";
              															       Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)
                                                 end                    										      
                    								  else  if !is_correct = 1
                  										       then  begin 
                          											      Printf.printf "verify_time: %f\n"  (pro_time_end-.pro_time_start);
                          											      Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "incorrect";
                  																		Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)	
                    												       end		
                  										else  begin
                  											     Printf.printf "verify_time: %f\n"  (pro_time_end-.pro_time_start);
                          									 Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "time_out";
                  													 Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)	
                  											    end
                  										;
                  										
                  										if(i=9) || (i=19) || (i=39) || (i=59) || (i=79) || (i=99) || (i=199) || (i=299) || (i=399) || (i=499) || (i=599)	|| (i=699) || (i=799) || (i=899) || (i=999)
                  									   then  begin  
                  											       Printf.printf "----------------------------------------前%d个---------------------------------------\n"  (i+1);
                  														 Printf.printf "time_cost:%f\n"  (pro_time_end-.time_start)
                  										       end
                  									   else ()							
                    								;																		
                    								 ) automata_pro_ary;								 
                    				  let time_end = 	Unix.gettimeofday () in 
                    					Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran);
															Printf.printf "refin_nums_total:%d\n" !ref_num_total;
                    					Printf.printf "runtime:%f\n"  (time_end-.time_start);	
                  				   end  ;
	
(*------------------------------------------------------------------------ 自动机求并   与程序自动机求交 取反求交 确定化  ----------------------------------------------------------------------*)						
(* 自动机求并   与程序自动机求交 取反求交 确定化 *)
if choose = 4
		    then begin				 		              			
                  let time_start = Unix.gettimeofday () in 			          
                 	let coll_automata = ref {start=0; receive = NumSet.empty; tran = TranMap.empty} in 
              		
              		let product_time = ref 0.0 in
              		let union_time = ref 0.0 in
									let ref_num_total = ref 0 in
                	(*tranMap_visualize	!coll_automata.tran; *)
                	flush stdout;						
                				 Array.iteri (fun i automata_pro ->
                					  (*对每一个程序执行下列流程*)
                						let pro_time_start = Unix.gettimeofday () in							
              							
              						(*	let instr_set = Automata.get_instr !rgx_arr.(i) in                                   (*此处设置不相关的语句仅是该程序的不相关语句*)
              							let instr_set = Automata.InstrSet.remove Execution.Skip instr_set in  *)
              							
                					  let is_correct = ref 0 in
                						let automata_pro = ref automata_pro  in 
                						let ref_num = ref 0 in                    			
              							let coll_automata_temp = ref {start=0; receive = NumSet.empty; tran = TranMap.empty}  in 
                				(*		Printf.printf "------------------------- program automata ---------------------\n";
                						Automata.tranMap_visualize !automata_pro.tran;
                						Printf.printf "start:%d\n" !automata_pro.start;
                						NumSet.iter (fun q0 -> Printf.printf "receive:%d\n" q0 ) !automata_pro.receive;
                						Printf.printf "----------------------------------------------------------------\n";  *)
                						
              							Printf.printf "--------------------------------------------demo%i---------------------------------------------------\n"  i;
                						while not (TranMap.is_empty !automata_pro.tran) && !is_correct=0 do
              								  let time_now = Unix.gettimeofday () in
              								(*	Printf.printf "states：%d\n"  (Automata.TranMap.cardinal !automata_pro.tran);  *)
              									
              											 if ( int_of_float (time_now -. pro_time_start) )> 200
              											    then  is_correct := 2
              													else  begin								
                                    						        (*先对求交验证*)			
              																																																																												
                                    										 if not (TranMap.is_empty !coll_automata.tran) && !ref_num = 0 
                                    										    then begin 					
              																								   	let product_start = Unix.gettimeofday () in					
              																										
																																  let automata_temp = Automata_utils.automata_product !automata_pro !coll_automata  in																																																																						
																																	if  not (TranMap.is_empty automata_temp.tran)		
																																	    then  begin
																																				      let automata_temp = Automata_utils.automata_determin  automata_temp in
																																					
																																							
																																				      let automata_temp = Automata_utils.comp_automata  automata_temp instr_set in
																																							automata_pro := Automata_utils.automata_product  !automata_pro  automata_temp;
																																					
																																				    end																								
                                    													    ;																																	            																																				
              																										let product_end = Unix.gettimeofday () in	
              																					         	Printf.printf "product_time: %f\n"  (product_end -. product_start);																							
              																						        product_time := ( !product_time +. (product_end -. product_start) );																		
                                    														 end
                                    												else ()
                                    											;
                                    										
                                    										 if (TranMap.is_empty  !automata_pro.tran)
                                    										   then ()
                                    											 else  begin
                                    													       (*抽取路径*)
                                    															(*	 Printf.printf "refindment %d: --------------------------------------------------------------------------------------\n " !ref_num ;   		
              																											 flush stdout;		*)							
                                    												         let execution = Automata_utils.get_execution !automata_pro in	 
                                  																	
                                  																(*	if i=5
																																		   then begin
																																				       Printf.printf "----------- 取到的路径 -------------\n";
                                              																 Array.iteri (fun i instr -> Printf.printf "%d--" i; Printf.printf "%s\n" (Execution.string_of_instr instr) ) execution;  
                                                                               flush stdout;  
																																				    end
																																						;  *)
                                    															 	  
                                    																														 
                                    																 (*判断是否为真反例*)
                                    																 let is_feasible = Coherence.is_feasible execution var_list fun_list in
                                    																  if is_feasible = 0
                                    			                                 then begin is_correct := 1; Array.iter (fun instr -> Printf.printf "%s\n" (Execution.string_of_instr instr) ) execution    end  
                                    					                             else begin 	 																								    																		 
                                    																				    (*对假反例泛化*)
                                    																				    let (gen_automata,_class) = Refinement.gen_automata  execution var_list fun_list instr_set is_feasible  in																																																								
                                    																						let gen_automata = Automata_utils.automata_determin  gen_automata in
              																																(*	Printf.printf "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n"; 
              																																	flush stdout;		*)
                                  																							
																																						 (*		if i=5
																																								   then  begin
																																										       Printf.printf "---------------- 泛化得到的自动机为: -------------------\n";
                                              																							Automata.tranMap_visualize gen_automata.tran;    
                          																																	NumSet.iter (fun q0 -> Printf.printf "receive:%d\n" q0 ) gen_automata.receive; 																																										    
																																										     end;         *)
																																												                        																																																						
                                    																					(*	Printf.printf "&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n";  
              																																	flush stdout;		*)
                                    																						(*取反*)
                                    																					  let comp_automata = Automata_utils.comp_automata  gen_automata instr_set in			
            																																    if not (i = Array.length automata_pro_ary-1) (* && (_class != 4 ) *)
																																								   then  begin 																																										       
																																										       coll_automata_temp := Automata_utils.automata_union  !coll_automata_temp gen_automata instr_set;																																													 
																																												 end
																																							     else  (); 
																																								
              																																(*	Printf.printf "comp*********************************************************\n";  
              																																	flush stdout;		*)
              																																																		
                                    																				    automata_pro := Automata_utils.automata_product  !automata_pro comp_automata;  
              																																	
              																																(*	Printf.printf "product*********************************************************\n";  
              																																	flush stdout;		*)
                                    																						ref_num := !ref_num+1;       
                                    																						end
                                                                    end   
              															 end  
                                    	done;																               										
              									  
																	let union_start = Unix.gettimeofday () in
																	
																	coll_automata_temp := Automata_utils.automata_determin !coll_automata_temp;  
																	coll_automata := Automata_utils.automata_union  !coll_automata !coll_automata_temp instr_set;
																	let union_end = Unix.gettimeofday () in
																	let pro_time_end = Unix.gettimeofday () in									
              										flush stdout;
																	
																	Printf.printf "union_time: %f\n"  (union_end -. union_start) ;
              										union_time := !union_time +. (union_end -. union_start); 
              										
                									Printf.printf "refindment nums:%d\n" !ref_num ;															
              									  ref_num_total := !ref_num_total + !ref_num;							
																																																																																												  								
                								  if !is_correct = 0
                									   then begin 
                											       Printf.printf "verify_time: %f\n"  (pro_time_end -. pro_time_start);
                											       Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "correct";
              															 Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)
                										      end
                								  else  if !is_correct = 1
              										       then  begin 
                      											      Printf.printf "verify_time: %f\n"  (pro_time_end-.pro_time_start);
                      											      Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "incorrect";
              																		Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)	
                												       end		
              										else  begin
              											     Printf.printf "verify_time: %f\n"  (pro_time_end-.pro_time_start);
                      									 Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "time_out";
              													 Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)	
              											    end
              										;												               										       									  								
              										
              										if(i=9) || (i=19) || (i=39) || (i=59) || (i=79) || (i=99) || (i=199) || (i=299) || (i=399) || (i=499) || (i=599)	|| (i=699) || (i=799) || (i=899) || (i=999)
              									   then  begin  
              											       Printf.printf "----------------------------------------前%d个---------------------------------------\n"  (i+1);
              														 Printf.printf "time_cost:%f\n"  (pro_time_end-.time_start);
              														 Printf.printf "product_time:%f\n"  !product_time;
              														 Printf.printf "product_time百分比:%f\n"  ( !product_time /. (pro_time_end-.time_start));
																					 Printf.printf "union_time:%f\n"  !union_time;
              														 Printf.printf "union_time百分比:%f\n"  ( !union_time /. (pro_time_end-.time_start));
              
              										       end
              									   else ()							
                								;																		
                								 ) automata_pro_ary;								 
                				  let time_end = 	Unix.gettimeofday () in 
              						Printf.printf "###########################################################################################";
                					Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran);
													Printf.printf "refin_nums_total:%d\n" !ref_num_total;
                					Printf.printf "runtime:%f\n"  (time_end-.time_start);																													
                          Printf.printf "product_time:%f\n"  !product_time;
              						Printf.printf "union_time:%f\n"  !union_time;
              						Printf.printf "product_time百分比:%f\n"  ( !product_time /. (time_end-.time_start) );
                          Printf.printf "union_time百分比:%f\n"  ( !union_time /. (time_end-.time_start) );
             end		;

(*-----------------------------------------------------------------------------------------------------------------------------------------------------------------*)		
(* 用inclusion的方法进行检查 *)				
if choose = 5
		    then begin				 		              			
                  let time_start = Unix.gettimeofday () in 			          
                 	let coll_automata = ref {start=0; receive = NumSet.empty; tran = TranMap.empty} in 
              		
              		let product_time = ref 0.0 in
              		let union_time = ref 0.0 in
                	(*tranMap_visualize	!coll_automata.tran; *)
                	flush stdout;						
                				 Array.iteri (fun i automata_pro ->
                					  (*对每一个程序执行下列流程*)
                						let pro_time_start = Unix.gettimeofday () in							
              							
              						(*	let instr_set = Automata.get_instr !rgx_arr.(i) in                                   (*此处设置不相关的语句仅是该程序的不相关语句*)
              							let instr_set = Automata.InstrSet.remove 					Execution.Skip instr_set in  *)
              							
                					  let is_correct = ref 0 in
                						let automata_pro = ref automata_pro  in 
                						let ref_num = ref 0 in     
                					  let union_time_pro = ref 0.0 in
              							let coll_automata_temp = ref {start=0; receive = NumSet.empty; tran = TranMap.empty}  in 
                				(*		Printf.printf "------------------------- program automata ---------------------\n";
                						Automata.tranMap_visualize !automata_pro.tran;
                						Printf.printf "start:%d\n" !automata_pro.start;
                						NumSet.iter (fun q0 -> Printf.printf "receive:%d\n" q0 ) !automata_pro.receive;
                						Printf.printf "----------------------------------------------------------------\n";  *)
                						
              							Printf.printf "--------------------------------------------demo%i---------------------------------------------------\n"  i;
                						while not (TranMap.is_empty !automata_pro.tran) && !is_correct=0 do
              								  let time_now = Unix.gettimeofday () in
              								(*	Printf.printf "states：%d\n"  (Automata.TranMap.cardinal !automata_pro.tran);  *)              									
              											 if ( int_of_float (time_now -. pro_time_start) )> 200
              											    then  is_correct := 2
              													else  begin							                                                    																																																																												
                          										let execution =  if not (TranMap.is_empty !coll_automata.tran)
                          										                     then begin 					
                        																								   	let product_start = Unix.gettimeofday () in																													
                        																										Automata_utils.is_contain  !automata_pro !coll_automata 
																																				end  
																																	 else  begin Automata_utils.get_execution !automata_pro end  in
																								    
																							if (Array.length execution = 0)
																							    then  automata_pro := {start=0; receive = NumSet.empty; tran = TranMap.empty}
																									else  begin
																										       let is_feasible = Coherence.is_feasible execution var_list fun_list in
                																           if is_feasible = 0
                        			                                 then begin is_correct := 1; Array.iter (fun instr -> Printf.printf "%s\n" (Execution.string_of_instr instr) ) execution    end  
                        					                             else begin 	 																																	    
																																    (* Printf.printf "----------- 取到的路径 -------------\n";
                                    																 Array.iteri (fun i instr -> Printf.printf "%d--" i; Printf.printf "%s\n" (Execution.string_of_instr instr) ) execution;  
                                                                     flush stdout; 		*)																				    																		 
                        																				    (*对假反例泛化*)
                        																				    let (gen_automata,_class) = Refinement.gen_automata  execution var_list fun_list instr_set is_feasible  in																																																								
                        																						let gen_automata = Automata_utils.automata_determin  gen_automata in  																													
                      																							
																																 (*		
																																		 Printf.printf "---------------- 泛化得到的自动机为: -------------------\n";
                      																							 Automata.tranMap_visualize gen_automata.tran;    
  																																	 NumSet.iter (fun q0 -> Printf.printf "receive:%d\n" q0 ) gen_automata.receive; 		*)
																																						                        																																																						
                        																					(*	Printf.printf "&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n";  
  																																	flush stdout;		*)
                        																						(*取反*)
                        																					  let comp_automata = Automata_utils.comp_automata  gen_automata instr_set in			
																																    if  not (i = Array.length automata_pro_ary-1) (* && (_class != 4 ) *)
																																		   then  begin 																																										       
																																				       coll_automata_temp := Automata_utils.automata_union  !coll_automata_temp gen_automata instr_set;																																													 
																																						 end
																																	     else  (); 
																																																																												
                        																				    automata_pro := Automata_utils.automata_product  !automata_pro comp_automata;  
  																																	
  																																(*	Printf.printf "product*********************************************************\n";  
  																																	flush stdout;		*)
                        																						ref_num := !ref_num+1;                                         																			
																														      end
																							        end																											  
              															 end  
                                   done;																               										
              									  
																	let union_start = Unix.gettimeofday () in															
																(*	coll_automata_temp := Automata_utils.automata_determin !coll_automata_temp;  *)
																  coll_automata := Automata_utils.automata_union  !coll_automata !coll_automata_temp instr_set;
																	let union_end = Unix.gettimeofday () in
																	let pro_time_end = Unix.gettimeofday () in									
              										flush stdout;
																	
																	Printf.printf "union_time: %f\n"  (union_end -. union_start) ;
              										union_time := !union_time +. (union_end -. union_start); 
              										
                									Printf.printf "refindment nums:%d\n" !ref_num ;															
              																																														  								
                								  if !is_correct = 0
                									   then begin 
                											       Printf.printf "verify_time: %f\n"  (pro_time_end -. pro_time_start);
                											       Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "correct";
              															 Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)
                										      end
                								  else  if !is_correct = 1
              										       then  begin 
                      											      Printf.printf "verify_time: %f\n"  (pro_time_end-.pro_time_start);
                      											      Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "incorrect";
              																		Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)	
                												       end		
              										else  begin
              											     Printf.printf "verify_time: %f\n"  (pro_time_end-.pro_time_start);
                      									 Printf.printf "demo%i is ******" i; Printf.printf "%s\n" "time_out";
              													 Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran)	
              											    end
              										;
              									
              										
              										if(i=9) || (i=19) || (i=39) || (i=59) || (i=79) || (i=99)	|| (i=199) || (i=299) || (i=399) || (i=499) || (i=599)	|| (i=699) || (i=799) || (i=899) || (i=999)
              									   then  begin  
              											       Printf.printf "----------------------------------------前%d个---------------------------------------\n"  (i+1);
              														 Printf.printf "time_cost:%f\n"  (pro_time_end-.time_start);
              														 Printf.printf "product_time:%f\n"  !product_time;
              														 Printf.printf "product_time百分比:%f\n"  ( !product_time /. (pro_time_end-.time_start));
																					 Printf.printf "union_time:%f\n"  !union_time;
              														 Printf.printf "union_time百分比:%f\n"  ( !union_time /. (pro_time_end-.time_start));
              
              										       end
              									   else ()							
                								;																		
                								 ) automata_pro_ary;								 
                				  let time_end = 	Unix.gettimeofday () in 
              						Printf.printf "###########################################################################################";
                					Printf.printf "states:%d\n"   (Automata.TranMap.cardinal !coll_automata.tran);
                					Printf.printf "runtime:%f\n"  (time_end-.time_start);																													
                          Printf.printf "product_time:%f\n"  !product_time;
              						Printf.printf "union_time:%f\n"  !union_time;
              						Printf.printf "product_time百分比:%f\n"  ( !product_time /. (time_end-.time_start) );
                          Printf.printf "union_time百分比:%f\n"  ( !union_time /. (time_end-.time_start) );
												(*	Automata.tranMap_visualize !coll_automata.tran;
													Printf.printf "start:%d\n" !coll_automata.start;
                					NumSet.iter (fun q0 -> Printf.printf "receive:%d\n" q0 ) !coll_automata.receive;  *)
             end																						






      let usage_message = "TO-DO add usage message"
      let choose = ref (-1)
      let filename = ref ""
      let input_files = ref []
      		
      let speclist = [
      	("-choose", Arg.Set_int choose, "what choose means");
      	("-filename", Arg.Set_string filename, "what filename means");
      	]
      	
      let anon_fun f = 
      	input_files:=f::!input_files
      	
      let () = 
      	Arg.parse speclist anon_fun usage_message;
      	main !choose !filename
