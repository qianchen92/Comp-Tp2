
type ident = string

type expression =
  | Plus of expression * expression
  | Minus of expression * expression
  | Mul of expression * expression
  | Div of expression * expression
  | Const of int
  | Expr_Ident of ident
  | ArrayElem of ident * expression
  | ECall of ident * expression array

type lhs =
  | LHS_Ident of ident
  | LHS_ArrayElem of ident * expression

type print_item =
  | Print_Expr of expression
  | Print_Text of string

type read_item = lhs

type dec_item =
  | Dec_Ident of ident
  | Dec_Array of ident * int

type declaration = dec_item list

type statement =
  | Assign of lhs * expression
  | Return of expression
  | SCall of ident * expression array
  | Print of print_item list
  | Read of read_item list
  | Block of declaration * statement list
  | If of expression * statement * statement option
  | While of expression * statement

type typ =
  | Type_Int
  | Type_Void

type param = ident

type proto = typ * ident * param array

type program_unit =
  | Proto of proto
  | Function of proto * statement

type program = program_unit list
