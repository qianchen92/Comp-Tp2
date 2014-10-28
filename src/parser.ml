
open Genlex

let lexer0 = make_lexer
    ["PROTO"; "FUNC";
     "INT"; "VOID";
     "("; ")"; "["; "]"; "{"; "}"; ":="; ",";
     "RETURN"; "PRINT"; "READ"; "IF"; "THEN"; "ELSE"; "FI"; "WHILE"; "DO"; "DONE";
     "+"; "-"; "*"; "/" ]

let lexer stream =
  let rec aux = parser
    | [< 'Int n when n<0; t=aux >] -> [< 'Kwd "-"; 'Int (-n); t >]
    | [< 'h; t=aux >] -> [< 'h; t >]
    | [< >] -> [< >] in
  aux (lexer0 stream)

(* p? *)
let opt p = parser
  | [< x = p >] -> Some x
  | [<>] -> None

(* p* *)
let rec many p = parser
  | [< x = p; l = many p >] -> x::l
  | [<>] -> []

(* p+ *)
let some p = parser
  | [< x = p; l = many p >] -> x::l

(* p (sep p)* *)
let rec list1 p sep = parser
  | [< x = p; l = list1_aux p sep >] -> x::l
and list1_aux p sep = parser
  | [< _ = sep; l = list1 p sep >] -> l
  | [<>] -> []

(* (p (sep p)* )? *)
let list0 p sep = parser
  | [< l = list1 p sep >] -> l
  | [<>] -> []

open Ast

let rec program = parser
  | [< lu = some unite; _ = Stream.empty >] -> lu
and unite = parser
  | [< 'Kwd "PROTO"; p = proto >] -> Proto p
  | [< 'Kwd "FUNC"; p = proto; body = statement >] -> Function (p,body)
and proto = parser
  | [< t = typ; 'Ident f; 'Kwd "(" ?? "in proto: ( expected"; params = list0 param comma; 'Kwd ")" ?? "in proto: ) expected" >] -> (t,f, Array.of_list params)
  | [< >] -> raise (Stream.Error "in proto: <type> expected after PROTO/FUNC")
and typ = parser
  | [< 'Kwd "INT" >] -> Type_Int
  | [< 'Kwd "VOID" >] -> Type_Void
and param = parser
  | [< 'Ident id >] -> id
and statement = parser
  | [< 'Kwd "RETURN"; e = expression >] -> Return e
  | [< 'Kwd "PRINT"; l = list1 print_item comma >] -> Print l
  | [< 'Kwd "READ"; l = list1 read_item comma >] -> Read l
  | [< 'Kwd "IF"; c = expression; 'Kwd "THEN" ?? "THEN expected"; t = statement;
	e_opt = opt (parser [< 'Kwd "ELSE"; e = statement >] -> e); 'Kwd "FI" ?? "FI expected" >] -> If (c,t,e_opt)
  | [< 'Kwd "WHILE"; c = expression; 'Kwd "DO" ?? "DO expected"; s = statement; 'Kwd "DONE" ?? "DONE expected" >] -> While (c,s)
  | [< 'Kwd "{"; d = declaration; l = some statement; 'Kwd "}" ?? "} expected" >] -> Block (d,l)
  | [< 'Ident id; res = statement_after_ident id >] -> res
and statement_after_ident id = parser
  | [< 'Kwd "("; args = list0 expression comma; 'Kwd ")" ?? "in procedure call: ) expected" >] -> SCall (id, Array.of_list args)
  | [< 'Kwd "["; e = expression; 'Kwd "]" ?? "in lhs: ] expected"; res = statement_assign (LHS_ArrayElem (id,e)) >] -> res
  | [< res = statement_assign (LHS_Ident id) >] -> res
and statement_assign lhs = parser
  | [< 'Kwd ":="; e = expression >] -> Assign (lhs,e)
and lhs = parser
    [< 'Ident id; res = lhs_after_ident id >] -> res
and lhs_after_ident id = parser
  | [< 'Kwd "["; e = expression; 'Kwd "]" ?? "in lhs: ] expected" >] -> LHS_ArrayElem (id,e)
  | [<>] -> LHS_Ident id
and expression = parser
  | [< e1 = fact; e = expression_aux e1 >] -> e
and expression_aux e1 = parser
  | [< 'Kwd "+"; e2 = fact; e = expression_aux (Plus (e1,e2)) >] -> e
  | [< 'Kwd "-"; e2 = fact; e = expression_aux (Minus (e1,e2)) >] -> e
  | [<>] -> e1
and fact = parser
    [< e1 = primaire; e = fact_aux e1 >] -> e
and fact_aux e1 = parser
  | [< 'Kwd "*"; e2 = primaire; e = fact_aux (Mul (e1,e2)) >] -> e
  | [< 'Kwd "/"; e2 = primaire; e = fact_aux (Div (e1,e2)) >] -> e
  | [<>] -> e1
and primaire = parser
  | [< 'Int x >] -> Const x
  | [< 'Ident id; res = primaire_after_ident id >] -> res
  | [< 'Kwd "("; e = expression; 'Kwd ")" ?? "in primaire: ) expected" >] -> e
and primaire_after_ident id = parser
  | [< 'Kwd "("; args = list0 expression comma; 'Kwd ")" ?? "in function '" ^ id ^ "' call: ) expected" >] -> ECall (id, Array.of_list args)
  | [< 'Kwd "["; e = expression; 'Kwd "]" ?? "in primaire: ] expected" >] -> ArrayElem (id,e)
  | [<>] -> Expr_Ident id
and print_item = parser
  | [< 'String text >] -> Print_Text text
  | [< e = expression >] -> Print_Expr e
and read_item = parser
    [< x = lhs >] -> x
and declaration = parser
    [< ll = many list_dec >] -> List.flatten ll
and list_dec = parser
    [< 'Kwd "INT"; l = list1 dec_item comma >] -> l
and dec_item = parser
    [< 'Ident id; res = dec_item_after_ident id >] -> res
and dec_item_after_ident id = parser
  | [< 'Kwd "["; 'Int n; 'Kwd "]" ?? "in dec_item: ] expected" >] -> Dec_Array (id,n)
  | [<>] -> Dec_Ident id
and comma = parser
    [< 'Kwd ",">] -> ()

let parse_channel p ch =
  p (lexer (Stream.of_channel ch))
