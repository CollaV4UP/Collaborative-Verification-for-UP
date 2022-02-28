open Automata
open Printf

 let parse_with_error lexbuf =                                          (*词法分析，语法分析,错误处理*)
    try Myparser.prog Mylexer.read lexbuf with
    | Mylexer.UnexpectedToken msg ->
      fprintf stderr "lexer error\n";
      None
    | Myparser.Error ->
      fprintf stderr "parser error\n";
      exit (-1)
  
  
  let parse_from_string content =
    let lexbuf = Lexing.from_string content in                           (*创建缓冲区*)
    match parse_with_error lexbuf with
  
    | Some prog ->                                                       (*prog 是去掉注释，去掉间隔之后的程序   *)
  		let (preamble_opt,stm) = prog in		
  		let env = Typechecker.typecheck prog in
      let vlst,dtd_list,ltl_list,ltd_list,stop_singleton = Typechecker.names preamble_opt env in
  		                                                                   (*vlst是变量名列表*)
  																																			 (*dtd_list，ltl_list，ltd_list是不同的函数名列表，区别未知*)
  																																			 (*DataToData ... *)
  																																			 (*stop_singleton未知用途，推测可能是不满足if条件的情况*)
  		
  		let var_list = vlst in
  		let fun_list = List.append (List.append dtd_list ltl_list) dtd_list in
  			(var_list, fun_list, prog, env)
  		
    | None -> failwith "Failed to parse"		
  
 let parse_from_file s =
    let ss = Core.In_channel.read_lines s in
    let content = Core.String.concat ss in                               (*将读取的文件连在一起*)
    parse_from_string content	

let  verification pro_add = 
	      
	      let var_list,fun_list,prog,env = parse_from_file pro_add in 
				let rgx = Execution.regexOfProg env prog in
				let instr_set = Automata.get_instr rgx in	                              	
	    	let instr_set = Automata.InstrSet.remove Execution.Skip instr_set in

				let automata_pro = Automata.pro_automata rgx in	
				let automata_pro =  Automata_utils.ocamlflat_utils automata_pro instr_set 1 in 
				
				let pro_time_start = Unix.gettimeofday () in							
				
			  let is_correct = ref 0 in
				let automata_pro = ref automata_pro  in 
					
				let refine_num = ref 0 in
				(* correct=0 代表程序正确*)	
				while not (TranMap.is_empty  !automata_pro.tran) && !is_correct=0 do
					  let time_now = Unix.gettimeofday () in
								 if ( int_of_float (time_now -. pro_time_start) )> 20
								    then  is_correct := 2
										else  begin								
    						                										
    										 if (TranMap.is_empty  !automata_pro.tran)
    										   then ()
    											 else  begin
    													       (*抽取路径*)									
    												         let execution = Automata_utils.get_execution !automata_pro in	 	
																		 refine_num	:= !refine_num + 1;																									 
    																 (*判断是否为真反例*)
    																 let is_feasible = Coherence.is_feasible execution var_list fun_list in
    																 if is_feasible = 0
    			                                 then begin is_correct := 1  end  
    					                             else begin 	 																								    																		 
    																				    (*对假反例泛化*)
    																				    let (gen_automata,_class) = Refinement.gen_automata  execution var_list fun_list instr_set is_feasible in																																																								
    																						let gen_automata = Automata_utils.automata_determin  gen_automata in
    																					  let comp_automata = Automata_utils.comp_automata gen_automata instr_set in																																		
    																				    automata_pro := Automata_utils.automata_product !automata_pro comp_automata     
    																						end
                                    end   
												 end
                	done;																 
			   (!is_correct, !refine_num)		
														
																																												  								
                    
									
									
									
									
									
									
									
									 