open Printf
open Automata

module StringSet = Set.Make(
  struct
    type t = string
    let compare  = Stdlib.compare        	
  end)
	
module NumSet = Set.Make(
  struct
    type t = int
    let compare = Stdlib.compare
  end)
	
(*-------------------------------------------------------- unit格式转成bpl格式  -----------------------------------------------------------------------*)	  

(*字符串 String 中是否包含字符串 s *)
let is_contains string s = 
	  let flag = ref false in
	  String.iteri (fun  i c ->
			         if c = s.[0] && i < ( (String.length string) - (String.length s) +1 )
							    then  begin  let sub = String.sub string i (String.length s) in
      									       if String.equal  sub s
      												    then flag := true
      													  else () 
												end
								  else  ()      ) string ;
		!flag


(*删除s中的 then ;*)
let  	delete_sub_str  s  sub =
	    if String.equal sub "then"
  			   then begin
  					      let loc = String.rindex s 't' in
  								(String.sub s 0 loc)^(String.sub s (loc+4) ( (String.length s) - (loc+4) )  )
  					    end
  				 else begin
  					      let loc = String.index s ';' in
  								(String.sub s 0 loc)^(String.sub s (loc+1)  (String.length s - (loc+1) )  )
  					    end	
			
(*向s中添加 ; =*)		
let   add_sub_str  s sub = 
			if String.equal  sub ";"
			   then begin
					      s^";"
					    end
				 else begin
					      let loc = String.index s '=' in
								(String.sub s 0 loc )^"="^(String.sub s loc  (String.length s - loc )  )
					    end 				
(*将 == 删成  = 号*)
let  delete_eq  s =
	    let loc = String.index s '=' in
			(String.sub s 0 loc ) ^ (String.sub s (loc+1)  (String.length s - loc -1 )  ) 
	
(*在 if 后面 添加 then*)	
let add_then s =
	  let loc = String.index s ')' in
		(String.sub s 0 (loc+1) )^" then "^(String.sub s (loc+1)  (String.length s - loc-1 )  )
						

let unit_to_bpl   unit_add = 
	  let rec rd_lines ic bpl flag =			
			  try  let s = input_line ic in			     
				     if (String.length s > 4)	&&  (  (String.equal  (String.sub s 0 5) "Reach") || (String.equal  (String.sub s 0 4) "init")  )
						    then  begin
									      if (String.equal  (String.sub s 0 4) "init")
												   then flag := true
													 else ()
													;
												rd_lines  ic bpl flag
									     end								
					  	else  if  String.contains  s ':'
							        then   if String.contains s ';'
											          then  begin
														           let bpl = bpl^s^"\n" in
																	     rd_lines  ic bpl flag
														          end
													      else  let bpl = bpl^(add_sub_str  s ";")^"\n" in
																      rd_lines  ic bpl flag
				              else   if (String.contains  s '}')										
                                then  
																	begin
																		 if !flag
																		    then  begin
																					      flag := false;
																					      rd_lines  ic bpl flag
																					    end
																				else   begin
          																		 if (String.contains  s ';')
          																		    then begin
          																	             let bpl = bpl^(delete_sub_str s ";")^"\n" in
          																				       rd_lines  ic bpl flag
          																						 end
          																			  else   let bpl = bpl^s^"\n" in
          																				       rd_lines  ic bpl flag
																							 end
																   end			
										  else   if  (String.contains  s 'i') && (String.contains  s 'f') && (String.contains  s 't')&& (String.contains  s 'h') && (String.contains  s 'e') && (String.contains  s 'n') 
											       then  begin
															          let s = delete_sub_str s "then"  in
																			  let s =	if  (String.contains  s '!')
																				              then  s
																											else  add_sub_str s "=" in
																	      let bpl = bpl^s^"\n" in
																				rd_lines  ic bpl flag
																   end	             
											else   if  (String.contains  s 'w') && (String.contains  s 'h') && (String.contains  s 'i')&& (String.contains  s 'l') && (String.contains  s 'e')
											            then  begin
																			let s =	if  (String.contains  s '!')
																			             then  s
																			  					 else  add_sub_str s "=" in
																	    let bpl = bpl^s^"\n" in
																		  rd_lines  ic bpl flag
																   end	
											else   if (String.contains  s 'a') && (String.contains  s 's') && (String.contains  s 'u')
												     then begin
																			let s =	if  (String.contains  s '!')
																			             then  s
																			  					 else  add_sub_str s "=" in
																		  let s = if  (String.contains  s ';')
																			            then s
																									else add_sub_str s ";" in
																	    let bpl = bpl^s^"\n" in
																		  rd_lines  ic bpl flag
																   end	
											else 	 rd_lines  ic bpl flag									   
				with End_of_file -> bpl
	      in
					
	  let ic = open_in unit_add in
		let bpl = "// simple example\n"^
			        "type A;\n"^
              "function f(x: A) returns (A);\n"^
              "function h(x: A) returns (A);\n"^
              "function ran(x: A) returns (A);\n"^
              "procedure main(){\n"^
              "     var x, y, t, k, z, m, w, w1, w2, w3, w4, s, v1, v2, v3, v4, v5, p1, p2, choose, zero, one, two: A;\n"  in
		let flag = ref false in
		let bpl = rd_lines  ic bpl flag in
		let bpl = bpl^"\nassert(x == y);" in
		let bpl = bpl^"\n}" in
		let loc_start = String.rindex  unit_add '/' in
		let loc_end = String.rindex  unit_add '.' in
		
		let bpl_name = (String.sub  unit_add  (loc_start+1) (loc_end-loc_start)   )^"bpl" in		
		let oc = open_out ("./benchmark_combin/"^bpl_name) in
		output_string  oc bpl



(*-------------------------------------------------------- bpl格式转成unit格式  -----------------------------------------------------------------------*)	  

  let bpl_to_unit   bpl_add =   
		 let rec rd_lines ic unit =
		     try  let s = input_line ic in		
				         if (is_contains s "type" || is_contains s "function" ||  is_contains s "var"  || is_contains s "proce" || is_contains s "//" || String.equal  (String.sub s 0 1) "{" || String.equal  (String.sub s 0 1) "}")
								    then  rd_lines ic unit
								  else if  (is_contains s "if")
									     then begin
												      let s = add_then s in
															let s = if ( is_contains s "==" )
															            then  delete_eq s  
																					else  s      in
															rd_lines ic (unit^s)
														end
									else if ( is_contains s "==" )
									  then  begin
											      let s = delete_eq s in
														rd_lines ic (unit^s)
												  end		
									else 	begin
										     let unit = unit^s in
										     rd_lines ic	unit	
												end		  
				  with End_of_file -> unit   
			in
				  
		  let ic = open_in bpl_add in  
			let unit =  "Reach([x,y,z,w,star,ret_x,ret_y,r,s,t,tmp,ret,w0,w1,z0,z1,t1,t2,ret_t1,ret_t2],[f,h],[x])\n"^
                  "init{\n"^
                  "}\n"    in
			let unit = rd_lines ic unit in
			
			let loc_start = String.rindex  bpl_add '/' in
		  let loc_end = String.rindex  bpl_add '.' in
      let unit_name = (String.sub  bpl_add  (loc_start+1) (loc_end-loc_start)   )^"unit" in		
		  let oc = open_out ("/home/dyd/project/github/BigAutomata/benchmark_fm/svcomp_unit/"^unit_name) in
		  output_string  oc unit
	
(*--------------------------------------------------------------------- 语句变异 ------------------------------------------------------------------------------------------*)	

let neg_con  stmt = 
	  let loc = String.index_opt stmt '!' in
		match loc with
		  | Some i -> (String.sub stmt 0 i)^(String.sub stmt (i+1) (String.length stmt - i - 1) )
			| None ->  let loc_eq = String.index stmt '=' in
			           (String.sub stmt 0 loc_eq )^"!"^(String.sub stmt loc_eq (String.length stmt - loc_eq)  )
				 
		 
(*对语句进行变异  总结几种变异方式   增量更新  *)
(*1、   x := f(x)  ->  y := f(y)   *)
(*2、   x := f(x)  ->  x := f(y) *)
(*3、   if(x != y) ->  if(x = y) *)
(*4、   x := y  ->   y := x *)
(*5、   去掉语句 *)
(*6、   添加语句 *)

let  stmt_mutation pro_add = 	
	 	 let rec rd_lines ic pro =			
			  try  let s = input_line ic in	
				     let s = String.trim s in		    
						 let pro = if String.length s >0
						              then  Array.append pro [|s|]
				                  else  pro    in
						 rd_lines ic pro							   
				with End_of_file -> pro
	      in		
	  let ic = open_in  pro_add in
		let pro = rd_lines  ic [||] in
				
		let var_list,fun_list,prog,env = Verification.parse_from_file  pro_add in
		let var_arr = Array.of_list var_list in
		let fun_arr = Array.of_list fun_list in
		
		let instr = List.fold_left (fun  instr x->
			                List.fold_left (fun instr y ->
														if not (String.equal x y) 
														   then  begin 
																        let instr = StringSet.add (x^" := "^y) instr in
																				let instr = StringSet.add ("assume("^x^" = "^y^")") instr in
																				StringSet.add ("assume("^x^" != "^y^")") instr
																		 end
															 else  instr     )  instr var_list   )  StringSet.empty var_list  in
		
		 let instr = List.fold_left (fun instr x ->
			                List.fold_left (fun instr y ->
														List.fold_left (fun instr f ->
															    StringSet.add  (x^" := "^f^"("^y^")") instr     																			
																					  )  instr fun_list   )  instr var_list  ) instr  var_list  in
																						
		 let instr = Array.of_list (StringSet.elements instr) in
		 let pro_mu = ref pro in
			
		 let num = ref 1 in
		 while !num < 10 do
				  Random.init (int_of_float (Unix.gettimeofday ()) + !num);					
				  let pro_mu_temp = ref !pro_mu in		
								
					for i = 0 to 0 (* (Random.int 2) *)  do		
						  let mutation_loc = ref ( (Random.int ( Array.length !pro_mu -3) ) +3 )  in
		            while (String.length !pro_mu.(!mutation_loc)  <  4 ) || (is_contains  !pro_mu.(!mutation_loc) "assert") || (is_contains  !pro_mu.(!mutation_loc) "else")  do
							      mutation_loc	:=  (Random.int ( Array.length !pro_mu -3) ) +3
			           done;
														
    					let pro_temp = ref [||] in  		
    								Array.iteri (fun i stmt ->
    									   if i = !mutation_loc
    										    then  begin
    													       if String.contains stmt ';' || String.contains stmt '{'
																		        then  begin  
																							      if  is_contains stmt "assume"   
																										    then  begin
																													      let num = Random.int 3 in
																													      if num = 0
																																     then  begin
																																			       let stmt_temp = neg_con stmt in
																																						 pro_temp := Array.append  !pro_temp  [|stmt_temp|]
																																			     end
																																else  if num = 1
																																        then pro_temp := Array.append  !pro_temp  [|stmt|]
																																else  let stmt_temp = instr.(Random.int (Array.length instr)  )^";" in
          																										         pro_temp := Array.append  !pro_temp  [|stmt_temp|]
																													    end
																										else if (is_contains stmt "while"  ||  is_contains stmt "if")
																											      then  begin
																													          if  Random.int 2 = 0
																																         then  begin
																																			          let stmt_temp = neg_con stmt in
																																						    pro_temp := Array.append  !pro_temp  [|stmt_temp|]
																																			         end
																																		      else  pro_temp := Array.append  !pro_temp  [|stmt|]
																													         end
																										else if is_contains stmt "skip"
																										      then  begin
																														       let num = Random.int 3 in
																														       if  num = 2
																																	     then  begin
																																				        let stmt_temp = instr.(Random.int (Array.length instr)  )^";" in
          																										                  pro_temp := Array.append  !pro_temp  [|stmt_temp|]
																																				     end
																														           else  pro_temp := Array.append  !pro_temp  [|stmt|]																																	
																														    end
																										else  if String.contains stmt '('
																										      then  begin
																														      let num = Random.int 4 in
																																	if num = 0
																																	   then  begin
																																				       let stmt_temp = instr.(Random.int (Array.length instr)  )^";" in
          																										                 pro_temp := Array.append  !pro_temp  [|stmt_temp|]																																			       
																																			     end
																																	else if num = 1
																																	    then  begin
																																				      let stmt_temp = instr.(Random.int (Array.length instr)  )^";" in
                        																										  pro_temp := Array.append  !pro_temp  [|stmt_temp|];
                        																										  pro_temp := Array.append  !pro_temp  [|stmt|]
																																				    end
																																	else if num = 2
																																	     then begin
																																				      let stmt_temp = "skip;" in
																																							pro_temp := Array.append  !pro_temp  [|stmt_temp|]
																																				    end
																																  else begin
																																				      let loc = String.index stmt '(' in
																																				      let stmt_temp = String.sub stmt 0 (loc+1) in
																																							let var = var_arr.(Random.int (Array.length var_arr) ) in
																																							let stmt_temp = stmt_temp^var^")"^";" in
																																							pro_temp := Array.append  !pro_temp  [|stmt_temp|]
																																				    end
																														    end
																										else          let num = Random.int 4 in
																																	if num = 0
																																	   then  begin
																																				       let stmt_temp = instr.(Random.int (Array.length instr)  )^";" in
          																										                 pro_temp := Array.append  !pro_temp  [|stmt_temp|]																																			       
																																			     end
																																	else if num = 1
																																	    then  begin
																																				      let stmt_temp = instr.(Random.int (Array.length instr)  )^";" in
                        																										  pro_temp := Array.append  !pro_temp  [|stmt_temp|];
                        																										  pro_temp := Array.append  !pro_temp  [|stmt|]
																																				    end
																																	else if num = 2
																																	     then begin
																																				      let stmt_temp = "skip;" in
																																							pro_temp := Array.append  !pro_temp  [|stmt_temp|]
																																				    end
																																	else begin
																																		   let loc1 = String.index stmt ':' in
																																	     let stmt_temp1 = String.sub stmt 0 loc1 in
																																			 let loc2 = String.index stmt ';' in
																																			 let stmt_temp2 = String.sub stmt (loc1+2) (loc2 - loc1-2) in
																																			 let stmt_temp = stmt_temp2^":="^stmt_temp1^";" in
																																			 pro_temp := Array.append  !pro_temp  [|stmt_temp|]
																								                       end
																						     end
													            else  begin
																				    let num = Random.int 3 in
																			      if num = 0
																						   then  begin
																									       let stmt_temp = instr.(Random.int (Array.length instr)  ) in
																				                 pro_temp := Array.append  !pro_temp  [|stmt_temp|]																																			       
																								     end
																						else if num = 1
																						    then  begin
																									      let stmt_temp = instr.(Random.int (Array.length instr)  )^";" in
  																										  pro_temp := Array.append  !pro_temp  [|stmt_temp|];
  																										  pro_temp := Array.append  !pro_temp  [|stmt|]
																									    end
																						else if num = 2
																						     then begin
																									      let stmt_temp = "skip" in
																												pro_temp := Array.append  !pro_temp  [|stmt_temp|]
																									    end
																					  end
    													    end
    										 else  pro_temp := Array.append  !pro_temp  [|stmt|]   ) !pro_mu_temp ;	
    				     pro_mu_temp := !pro_temp
						done;
						let loc_temp = String.rindex pro_add '0' in
						let pro_add = String.sub  pro_add 0 loc_temp in
      			let pro_add = pro_add ^ (Core.Int.to_string !num) ^ ".unit" in
						
					begin																	
              try
          			let s = Array.fold_left (fun s stmt -> 
          									s^stmt^"\n"  ) "" !pro_mu_temp in
                			  let oc = open_out  pro_add  in
                				output_string  oc s;
                			  close_out oc
                 with _ ->
                		failwith "file_writing error"  
					end;
					      
        			  let (is_correct,ref_num) = Verification.verification pro_add in
        				if  is_correct = 0
        				    then  begin (*Printf.printf "%d--\n" !num;*) num := !num+1; pro_mu := !pro_mu_temp;  flush stdout end 
        						else  ()        
		  done				
		
(*--------------------------------------------------------------------------------------------------------------------------------------*)		
 let printf_file pro_arr = 	 	
	   Array.iteri(fun i block ->
						
						let s = ref ("Reach([x,y,t,k,m,z,w,w1,w2,w3,w4,s,v1,v2,v3,v4,v5,p1,p2,choose,zero,one,two],[f,h,ran],[x])\n") in  
        		        s := !s^"init{\n }\n"; 
										 s := !s^"assume(x = y);\n";	  
										s := !s ^ "assume(zero != one);\n"
										        ^ "assume(zero != two);\n"
														^ "assume(one != two);\n";		
						s := !s^block^";\n";							    
                  							
					 	s := !s^"assert(x = y)";  
						try
              let oc = open_out ("benchmark_combin/benchmark"^(Core.Int.to_string i) ^ ".unit")  in
              output_string  oc !s;
              close_out oc
            with _ ->
              failwith "file_writing error"        )pro_arr 

																			                                     	
(*两个程序顺序拼接    嵌套进两个if块中并行   分别放在 if 分支和 else 分支中   生成500个全为正确的程序的代码*)
let  block_mutation () = 
	
		 let rec rd_lines ic bpl =			
			      try  let s = input_line ic in			     
				         if  ( String.length s ) > 3 && ( String.equal  (String.sub  s 0 2) "(*" ) 
						          then 	rd_lines  ic bpl	
			 					      else  begin
									           let bpl = bpl^s^"\n"  in
									           rd_lines  ic bpl
									          end   
						with  End_of_file ->	 bpl	
				    in					
		
		 let pro_arr = ref [||] in							
  	 for i=0 to 9 do
			     let pro = ref "" in
			     let pro_add = "/home/dyd/project/github/BigAutomata/benchmark_combin/frag/n_frag"^(Core.Int.to_string i)^".unit" in			
	         let ic = open_in  pro_add in
		       let pro = rd_lines  ic "" in
					 pro_arr := Array.append  !pro_arr [|pro|]
			done;																										 
											
		 let condition_arr = Array.of_list ["s=v1";"s=v2";"s=v3";"s=v4";"s=v5"] in
		 let while_condition_arr = Array.of_list ["s!=k1";"s!=k2";"s!=k3";"s!=k4";"s!=k5"] in
		 Random.init (int_of_float (Unix.gettimeofday ()) );	
			
		 let num_set = ref NumSet.empty in
		 num_set := NumSet.add 3 !num_set;


		for i=0 to 489 do
			    let num = (Random.int 2 + 1)in
					let block = ref "" in
					
					let flag = ref false in
					for j=0 to num do
						 if j=0
						    then   block := !block ^ "if(choose = zero)" ^ "then{\n" ^ !pro_arr.(Random.int 10 )  
						 else if j=1
						    then   block := !block ^ "if(choose = one)" ^ "then{\n" ^ !pro_arr.(Random.int 10)		
						 else if j=2
					      then   block := !block ^ "if(choose = two)" ^ "then{\n" ^ !pro_arr.(Random.int 10 )			
						(* else if j=3
						    then   block := !block ^ "if(choose = three)" ^ "then{\n" ^ !pro_arr.(Random.int 10 )		*)
						 else ()   ;
																
						 if  (Random.int 2) = 1  && not !flag
		              then begin
										    if j < num
												   then  
														  begin
        										     let num_temp = (Random.int (num - j)) + j + 1 in
        										     if num_temp = 0
        												    then ()
        												 else if num_temp = 1
        												    then  begin 
																			      block :=  !block ^ ";\n" ^ "  choose := one\n";
																						flag := true
																					end
        												 else if num_temp = 2
        										        then begin 
																			      block :=  !block ^ ";\n" ^ "  choose := two\n" ;
																						flag := true
																				 end
        												(* else if num_temp = 3	
        														then block :=  !block ^ ";\n" ^ "  choose := three\n" *)
        												 else  ()
															end
											 end
									else  ()   ;
							block := !block ^ "}else{\n" ;
						  block := !block ^ "  skip\n};\n\n";				                                                       					  											
						done;						
						
						if(num = 1)
						   then  block := !block ^"if(choose != zero)then{\n"
        										         ^"   if(choose != one)then{\n"
        													   ^"             assume(x = y)\n"
        													   ^"    }else{\n"
        													   ^"      skip\n}\n"
        													   ^" }else{\n"
        													   ^"  skip\n}\n";
						if(num = 2)
						   then block := !block ^"if(choose != zero)then{\n"
        										        ^"   if(choose != one)then{\n"
        													  ^"      if(choose != two)then{\n"
        													  ^"             assume(x = y)\n"
        													  ^"           }else{\n"
        													  ^"             skip\n  }\n"
        													  ^"    }else{\n"
        													  ^"      skip\n}\n"
        													  ^" }else{\n"
        													  ^"  skip\n}\n";
						
				 pro_arr := Array.append !pro_arr [|!block|]
			done;	  
     printf_file !pro_arr
  		 
(*------------------------------------------------------------------ if组合方式 ---------------------------------------------------------------*)						

 let printf_file1 pro pro_add = 	 	

			       let s = ref ("Reach([x,y,t,k,m,z,s,v1,v2,v3,v4,v5,w,w1,w2,w3,w4,p1,p2,zero,one],[f,h,ran],[x])\n") in  				
        		     s := !s^"init{\n }\n";  
								 s := !s^"assume(x = y);\n";						    
                 s := !s^pro^";\n";						
					 	     s := !s^"assert(x = y)";  
						try
              let oc = open_out  pro_add  in
              output_string  oc !s;
              close_out oc
            with _ ->
              failwith "file_writing error"     
    
																			                                 	
let  block_mutation1 count = 																				
				
		 let rec rd_lines ic bpl =			
			      try  let s = input_line ic in			     
				         if  ( String.length s ) > 3 && ( String.equal  (String.sub  s 0 2) "(*" ) 
						          then 	rd_lines  ic bpl	
			 					      else  begin
									           let bpl = bpl^s^"\n"  in
									           rd_lines  ic bpl
									          end   
						with  End_of_file ->	 bpl	
				    in					
		
		 let pro_arr = ref [||] in							
  	 for i=0 to 8 do
			     let pro_add = "benchmark_combin/frag"^(Core.Int.to_string count)^"/frag/frag"^(Core.Int.to_string i)^".unit" in			
	         let ic = open_in  pro_add in
		       let pro = rd_lines  ic "" in
					 pro_arr := Array.append  !pro_arr [|pro|]
			done;																										 								
											
		 let condition_arr = Array.of_list ["s=v1";"s=v2";"s=v3";"s=v4";"s=v5"] in
		 let while_condition_arr = Array.of_list ["s!=k1";"s!=k2";"s!=k3";"s!=k4";"s!=k5"] in
     
		 let  nfrag_right_num = ref 0 in
		 let  nfrag_false_num = ref 0 in
		 let  nfrag_num = ref 0 in
		
		 while !nfrag_num  < 10 do
			   Unix.sleep 3;
    		 let num = Random.int 2  in
         let num1 = ref 0 in
				 let num2 = ref 0 in
				 
				 num1 := Random.int 9;
				 num2 := Random.int 9;
										 					
    		 let block =	ref "" in
					if num=0		
               then	 
								 begin 
        						  block := !block ^ "if("^condition_arr.(Random.int 5)^")then{\n" ^ !pro_arr.( !num1 )
        			                       ^"\n  }else{\n skip \n};\n";
        							block := !block ^ "if("^condition_arr.(Random.int 5)^")then{\n" ^ !pro_arr.( !num2 )
        			                       ^"\n  }else{\n skip \n};\n"; 
        							block := !block ^ !pro_arr.( Random.int 9) 
        				 end   ; 
								
         if num=1  then
            	 begin 
      				   block := "if("^condition_arr.(Random.int 5)^")then{\n" ^ !pro_arr.( !num1 )
      			                         ^"\n  }else{\n skip \n};\n"; 
      					 block := !block ^ !pro_arr.( !num2 )
      			                         ^";\n";
      					 block := !block ^ "if("^condition_arr.(Random.int 5)^")then{\n" ^ !pro_arr.( Random.int 9 )
      			                         ^"\n  }else{\n skip \n};\n"; 
      					 block := !block ^ !pro_arr.( Random.int 9)                 
            	 end;
				 printf_file1 !block ("benchmark_combin/temp.unit");					
				
				 let (is_correct,ref_num) = Verification.verification  ("benchmark_combin/temp.unit") in		
				 if is_correct = 0  && ref_num > 15 && ref_num < 70 &&  !nfrag_right_num < 8
				    then begin
							   	 begin
    								  try
                          let oc = open_out  ("benchmark_combin/frag"^(Core.Int.to_string count)^"/frag/n_frag"^(Core.Int.to_string  !nfrag_num )^".unit"   )  in
                          output_string  oc !block;
                          close_out oc
                      with _ ->
                          failwith "file_writing error" 
									 end;
									nfrag_num := !nfrag_num + 1;
									nfrag_right_num := !nfrag_right_num + 1;
								 end	
						;				
							
				 if is_correct = 1  && ref_num > 10 && ref_num < 40 &&  !nfrag_false_num < 2
				    then 	begin 
										begin
    										try
                          let oc = open_out  ("benchmark_combin/frag"^(Core.Int.to_string count)^"/frag/n_frag"^(Core.Int.to_string  !nfrag_num )^".unit"  )  in
                          output_string  oc !block;
                          close_out oc
                        with _ ->
                          failwith "file_writing error" 
										end ;
										nfrag_num := !nfrag_num + 1;
									  nfrag_false_num := !nfrag_false_num + 1;
									end																									   									  
		done   	
    


(*打乱程序顺序*)
let random_programs () =
	  let rec rd_lines ic pro =			
			      try  let s = input_line ic in			     
				         let pro = pro^s^"\n"  in
									rd_lines  ic pro								   
						with  End_of_file ->	 pro	
				    in	
		
		let pro_arr = ref [||] in
		for i=0 to 999 do
			  let pro_add = "/home/dyd/project/github/BigAutomata/benchmark_combin/frag5/seq0/benchmark" ^ (Core.Int.to_string i)^".unit"  in
				let ic = open_in  pro_add in
		    let pro = rd_lines  ic "" in
				pro_arr := Array.append !pro_arr [|pro|]
			done;
     

		let num_arr = ref [||] in
	  for i=0 to 999 do
			  num_arr := Array.append  !num_arr [|i|]
			done;
		for i=1 to 15 do
			  Unix.sleep 3;
    		let num_arr_temp = ref (!num_arr) in	
    		let count = ref 0 in	
    			while  not (Array.length !num_arr_temp = 0 )  do
    			  let loc = Random.int  (Array.length !num_arr_temp) in
    			 	Printf.printf "%d\n" !num_arr_temp.(loc); 
    			 begin
              try
                let oc = open_out ( "/home/dyd/project/github/BigAutomata/benchmark_combin/frag5/seq"^(Core.Int.to_string i)^"/benchmark" ^(Core.Int.to_string !count) ^ ".unit")  in
      					count := !count+1;
                output_string  oc !pro_arr.(!num_arr_temp.(loc));
                close_out oc
              with _ ->
                begin failwith "file_writing error"  end;
    			 end;
    				num_arr_temp := Array.append  (Array.sub  !num_arr_temp 0  loc)  (Array.sub !num_arr_temp (loc+1)  ( (Array.length !num_arr_temp)-loc-1 ) )  ;						
    			done	;
					Printf.printf "*******************************"
    done
	
	
	
(*---------------------------------------------------------------- 得到1000个正确和错误都有的benchmark -----------------------------------------------------------------*)

 let printf_file_temp  pro_add pro = 	 	
						
			let s = ref ("Reach([x,y,t,k,m,z,w,w1,w2,w3,w4,s,v1,v2,v3,v4,v5,p1,p2,choose,zero,one,two],[f,h,ran],[x])\n") in  
  		        s := !s^"init{\n }\n"; 
							s := !s^"assume(x = y);\n";	  
							s := !s ^ "assume(zero != one);\n"
							        ^ "assume(zero != two);\n"
											^ "assume(one != two);\n";		
			s := !s^pro^";\n";							    
            							
		 	s := !s^"assert(x = y)";  
			try
       (* let oc = open_out ("benchmark_combin/benchmark"^(Core.Int.to_string i) ^ ".unit")  in  *)
			  let oc = open_out pro_add  in
        output_string  oc !s;
        close_out oc
      with _ ->
        failwith "file_writing error"       

(*两个程序顺序拼接    嵌套进两个if块中并行   分别放在 if 分支和 else 分支中*)
let  block_mutation_temp () = 
	
	   for count=2 to 11 do
        	   (*读取文件*)
        		 let rec rd_lines ic bpl =			
        			      try  let s = input_line ic in			     
        				         if  ( String.length s ) > 3 && ( String.equal  (String.sub  s 0 2) "(*" ) 
        						          then 	rd_lines  ic bpl	
        			 					      else  begin
        									           let bpl = bpl^s^"\n"  in
        									           rd_lines  ic bpl
        									          end   
        						with  End_of_file ->	 bpl	
        				    in					
        		 (*自动合成基本程序*)
        		
        		 block_mutation1 count;
        		
        		 (*自动合成相似程序*)
        		 let pro_arr = ref [||] in							
          	 for i=0 to 9 do
        			     let pro = ref "" in
        			     let pro_add = "/home/dyd/project/github/BigAutomata/benchmark_combin/frag"^(Core.Int.to_string count)^"/frag/n_frag"^(Core.Int.to_string i)^".unit" in			
        	         let ic = open_in  pro_add in
        		       let pro = rd_lines  ic "" in
        					 pro_arr := Array.append  !pro_arr [|pro|]
        			done;																										 
        											
        		 let condition_arr = Array.of_list ["s=v1";"s=v2";"s=v3";"s=v4";"s=v5"] in
        		 let while_condition_arr = Array.of_list ["s!=k1";"s!=k2";"s!=k3";"s!=k4";"s!=k5"] in
        			
             let count_correct = ref 0 in
        		 let count_incorrect = ref 0 in
             let i = ref 0 in
        		 
        		while (!i < 1000)  do
        			    Unix.sleep 3;
        			    let num = (Random.int 2 + 1)in
        					let block = ref "" in
        					
        					let flag = ref false in
        					for j=0 to num do
        						 if j=0
        						    then   block := !block ^ "if(choose = zero)" ^ "then{\n" ^ !pro_arr.(Random.int 10 )  
        						 else if j=1
        						    then   block := !block ^ "if(choose = one)" ^ "then{\n" ^ !pro_arr.(Random.int 10)		
        						 else if j=2
        					      then   block := !block ^ "if(choose = two)" ^ "then{\n" ^ !pro_arr.(Random.int 10 )			
        						(* else if j=3
        						    then   block := !block ^ "if(choose = three)" ^ "then{\n" ^ !pro_arr.(Random.int 10 )		*)
        						 else ()   ;
        																
        						 if  (Random.int 2) = 1  && not !flag
        		              then begin
        										    if j < num
        												   then  
        														  begin
                										     let num_temp = (Random.int (num - j)) + j + 1 in
                										     if num_temp = 0
                												    then ()
                												 else if num_temp = 1
                												    then  begin 
        																			      block :=  !block ^ ";\n" ^ "  choose := one\n";
        																						flag := true
        																					end
                												 else if num_temp = 2
                										        then begin 
        																			      block :=  !block ^ ";\n" ^ "  choose := two\n" ;
        																						flag := true
        																				 end
                												(* else if num_temp = 3	
                														then block :=  !block ^ ";\n" ^ "  choose := three\n" *)
                												 else  ()
        															end
        											 end
        									else  ()   ;
        							block := !block ^ "}else{\n" ;
        						  block := !block ^ "  skip\n};\n\n";				                                                       					  											
        						done;						
        						
        						if(num = 1)
        						   then  block := !block ^"if(choose != zero)then{\n"
                										         ^"   if(choose != one)then{\n"
                													   ^"             assume(x = y)\n"
                													   ^"    }else{\n"
                													   ^"      skip\n}\n"
                													   ^" }else{\n"
                													   ^"  skip\n}\n";
        						if(num = 2)
        						   then block := !block ^"if(choose != zero)then{\n"
                										        ^"   if(choose != one)then{\n"
                													  ^"      if(choose != two)then{\n"
                													  ^"             assume(x = y)\n"
                													  ^"           }else{\n"
                													  ^"             skip\n  }\n"
                													  ^"    }else{\n"
                													  ^"      skip\n}\n"
                													  ^" }else{\n"
                													  ^"  skip\n}\n";
        						
								 let pro_add = "benchmark_combin/frag"^(Core.Int.to_string count)^"/benchmark"^(Core.Int.to_string !i) ^ ".unit" in																										
        				 printf_file_temp  pro_add !block;
        				 	
                 let (is_correct,ref_num) = Verification.verification pro_add in
                 if  is_correct = 0 && !count_correct < 500 
        				     then   begin
        							        i := !i + 1;
        											Printf.printf "--%d\n" !i;  
        											count_correct := !count_correct + 1
        							      end
        							;
        							
        				 if   is_correct = 1  &&  !count_incorrect < 500
        				     then  begin
        							        i := !i + 1;
        											Printf.printf "--%d\n" !i;  
        											count_incorrect := !count_incorrect + 1
        							     end			
        			done
			done
		
		
		