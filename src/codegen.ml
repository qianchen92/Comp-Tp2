open Ast

exception TODO (* to be used for actions remaining to be done *)
exception Error of string (* to be used for semantic errors *)

(* global context, main module, and builder for generating code *)

let context = Llvm.global_context ()
let the_module = Llvm.create_module context "main"
let builder = Llvm.builder context

(* LLVM types for VSL+ *)

let int_type = Llvm.i32_type context
let void_type = Llvm.void_type context
let char_type = Llvm.i8_type context
let string_type = Llvm.pointer_type char_type
let int_array_type = Llvm.array_type int_type 0

(* generation of constant integer LLVM values *)

let const_int n = Llvm.const_int int_type n

let zero_int = const_int 0

(* generation of constant string LLVM values *)

let const_string =
  let string_gep_indices = [|zero_int; zero_int|] in
  fun s ->
    let const_s = Llvm.const_stringz context s in
    let global_s = Llvm.define_global s const_s the_module in
    Llvm.const_gep global_s string_gep_indices

(* the printf function as a LLVM value *)

let func_printf =
  let tf = Llvm.var_arg_function_type int_type [|string_type|] in
  let f = Llvm.declare_function "printf" tf the_module in
  Llvm.add_function_attr f Llvm.Attribute.Nounwind;
  Llvm.add_param_attr (Llvm.param f 0) Llvm.Attribute.Nocapture;
  f

(* the scanf function as a LLVM value *)

let func_scanf =
  let tf = Llvm.var_arg_function_type int_type [|string_type|] in
  let f = Llvm.declare_function "scanf" tf the_module in
  Llvm.add_function_attr f Llvm.Attribute.Nounwind;
  Llvm.add_param_attr (Llvm.param f 0) Llvm.Attribute.Nocapture;
  f

(* Create an alloca instruction in the entry block of the
function. This is used for mutable local variables. *)

let create_entry_block_alloca the_function var_name typ =
  let builder = Llvm.builder_at context (Llvm.instr_begin (Llvm.entry_block the_function)) in
  Llvm.build_alloca typ var_name builder

let create_entry_block_array_alloca the_function var_name typ size =
  let builder = Llvm.builder_at context (Llvm.instr_begin (Llvm.entry_block the_function)) in
  let vsize = Llvm.const_int int_type size in
  Llvm.build_array_alloca typ vsize var_name builder

(* generation of code for each VSL+ construct *)

let rec gen_expression : expression -> Llvm.llvalue = function
  | Plus (e1,e2) ->
     let t1 = gen_expression e1 in
     (* generates the code for [e1] and returns the result llvalue *)
     let t2 = gen_expression e2 in
     (* the same for e2 *)
     Llvm.build_add t1 t2 "plus" builder
  (* appends an 'add' instruction and returns the result llvalue *)
  | Minus (e1,e2) ->
     let t1 = gen_expression e1 in
     (* generates the code for [e1] and returns the result llvalue *)
     let t2 = gen_expression e2 in
     (* the same for e2 *)
     Llvm.build_sub t1 t2 "minus" builder
  (* appends an 'minus' instruction and returns the result llvalue *)
  | Mul (e1,e2) ->
     let t1 = gen_expression e1 in
     (* generates the code for [e1] and returns the result llvalue *)
     let t2 = gen_expression e2 in
     (* the same for e2 *)
     Llvm.build_mul t1 t2 "mul" builder
  (* appends an 'mul' instruction and returns the result llvalue *)
  | Div (e1,e2) ->
     let t1 = gen_expression e1 in
     (* generates the code for [e1] and returns the result llvalue *)
     let t2 = gen_expression e2 in
     (* the same for e2 *)
     Llvm.build_udiv t1 t2 "div" builder
  | Const n ->
     const_int n
  (* returns a constant llvalue for that integer *)
  | Expr_Ident id ->
     SymbolTableList.lookup(id)
  | ECall (id, args) ->
     
     let callee =
       match Llvm.lookup_function id the_module with
       | Some callee -> callee
       | None -> raise (Error "unknown function referenced")
     in
     let params = Llvm.params callee in
     
     (* If argument mismatch error. *)
     if Array.length params != Array.length args then
       raise (Error "incorrect # arguments passed");
     let args = Array.map gen_expression args in
     Llvm.build_call callee args "calltmp" builder
  (* appends an 'div' instruction and returns the result llvalue *)
  | _ ->
     Printf.printf "gen_expression";
     raise TODO

let rec gen_declaration the_function : declaration -> unit = function
  | [] -> ()
  | (Ast.Dec_Ident hd_str)::tail ->
     let emplacement = create_entry_block_alloca the_function hd_str int_type in
     SymbolTableList.add hd_str emplacement
			 
  | (Ast.Dec_Array (hd_str,num)):: tail ->
     let emplacement = create_entry_block_array_alloca the_function hd_str int_array_type num in
     SymbolTableList.add hd_str emplacement
     
let rec gen_statement the_function: statement -> unit = function
  | Assign (LHS_Ident(l1),e1) -> 
      let t1 = gen_expression e1 in
      let emplacement = SymbolTableList.lookup(l1) in
      ignore(Llvm.build_store emplacement t1 builder)
  | Return expr ->
     let value = gen_expression expr in
     ignore (Llvm.build_ret value builder)
  | SCall (id, args) ->
     
     let callee =
       match Llvm.lookup_function id the_module with
       | Some callee -> callee
       | None -> raise (Error "unknown function referenced")
     in
     let params = Llvm.params callee in
     
     (* If argument mismatch error. *)
     if Array.length params != Array.length args then
       raise (Error "incorrect # arguments passed");
     let args = Array.map gen_expression args in
     ignore(Llvm.build_call callee args "calltmp" builder)

  | Print (itList) ->
     

	    
  | Block (d1, stList) ->
      SymbolTableList.open_scope();
      gen_declaration the_function d1;
      List.iter (gen_statement the_function) stList;
      SymbolTableList.close_scope()
  | If(cond,then_, else_option) ->
      let cond = gen_expression cond in
      let cond_val = Llvm.build_icmp Llvm.Icmp.Eq cond zero_int "ifcond" builder in
      let start_bb = Llvm.insertion_block builder in
      let the_function = Llvm.block_parent start_bb in

      let then_bb = Llvm.append_block context "then" the_function in
      Llvm.position_at_end then_bb builder;
      ignore(gen_statement the_function then_ );
      let new_then_bb = Llvm.insertion_block builder in
      
      let else_bb = Llvm.append_block context "else" the_function in
      Llvm.position_at_end else_bb builder;
      begin
        match else_option with
        | None -> 
          let new_else_bb = Llvm.insertion_block builder in
          let merge_bb = Llvm.append_block context "ifcont" the_function in
          Llvm.position_at_end merge_bb builder;

          ignore (Llvm.build_cond_br cond_val then_bb else_bb builder);
          Llvm.position_at_end new_then_bb builder; 
          ignore (Llvm.build_br merge_bb builder);
          Llvm.position_at_end new_else_bb builder; 
          ignore (Llvm.build_br merge_bb builder);

          Llvm.position_at_end merge_bb builder;
          
        | Some else_ ->
          ignore(gen_statement the_function else_);
          let new_else_bb = Llvm.insertion_block builder in
          let merge_bb = Llvm.append_block context "ifcont" the_function in
      
          Llvm.position_at_end start_bb builder;
          ignore (Llvm.build_cond_br cond_val then_bb else_bb builder);
          
          Llvm.position_at_end new_then_bb builder; 
          ignore (Llvm.build_br merge_bb builder);
          Llvm.position_at_end new_else_bb builder; 
          ignore (Llvm.build_br merge_bb builder);

          Llvm.position_at_end merge_bb builder;
      end
	
  | While (cond,prog) ->
      let cond = gen_expression cond in
      let cond_val = Llvm.build_icmp Llvm.Icmp.Eq cond zero_int "whilecond" builder in

      let start_bb = Llvm.insertion_block builder in
      let the_function = Llvm.block_parent start_bb in

      let do_bb = Llvm.append_block context "do" the_function in
      Llvm.position_at_end do_bb builder;
      ignore(gen_statement the_function prog);
      
      
      let done_bb = Llvm.append_block context "done" the_function in
      
      Llvm.position_at_end do_bb builder;
      ignore(Llvm.build_br done_bb builder);
      
      Llvm.position_at_end start_bb builder;
      ignore(Llvm.build_cond_br cond_val do_bb done_bb builder);
      Llvm.position_at_end done_bb builder
    
    
  | _ ->
     raise TODO

(** [type_llvm type_] return the llvm's type of the predefined type typ*)
let type_llvm type_ =
  match type_ with
  |Type_Int -> int_type
  |Type_Void -> void_type


let gen_proto proto_ =
  match proto_ with
  |(type_,ident_,args_) ->
    
     let int_ = Array.make (Array.length args_) int_type in
     let returnType = type_llvm type_ in
     let ft = Llvm.function_type returnType int_ in
     let f =
       match Llvm.lookup_function ident_ the_module with
       | None ->
	  Llvm.declare_function ident_ ft the_module
       | Some f ->
	      if Array.length (Llvm.basic_blocks f) == 0 then () else
		raise (Error "redefinition of function");
	      if Array.length (Llvm.params f) == Array.length args_ then () else
		raise (Error "redefinition of function with different # args");
	      f
     in
     f


(** [gen_function prog] generate code of the function prog*)
let rec gen_function : program_unit -> unit = function
  | Proto (type_,ident_,args_) ->
     ignore(gen_proto (type_,ident_,args_))
  | Function (proto,statement_) ->
     (*SymbolTableList.open_scope();*)
     let the_function = gen_proto proto in
     let (_,_,args_) = proto in
     let bb = Llvm.append_block context "entry"  the_function in
     Llvm.position_at_end bb builder;
     match statement_ with
     |Block (dec,statList) ->
       SymbolTableList.open_scope();
       Array.iteri (fun i a ->
		  let n = args_.(i) in
		  Llvm.set_value_name n a;
		  SymbolTableList.add n a;
		   ) (Llvm.params the_function);
       gen_declaration the_function dec;
       List.iter (gen_statement the_function) statList;
       SymbolTableList.close_scope()
     |_ -> raise (Error "missing {} after a function")
     (*SymbolTableList.close_scope()*)
     
       
	       
		   




(* function that turns the code generated for an expression into a valid LLVM code *)
let gen e : unit =
  (*let the_function = Llvm.declare_function "main" (Llvm.function_type int_type [||]) the_module in
  let bb = Llvm.append_block context "entry" the_function in
  Llvm.position_at_end bb builder;
  (*let x = gen_expression e in
  ignore (Llvm.build_ret x builder)*)
  (*gen_statement the_function e;
  ignore (Llvm.build_ret_void builder)*)*)
  List.iter gen_function e
