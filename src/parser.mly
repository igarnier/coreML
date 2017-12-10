%{
  
%}

%token TYPEARROW TYPEPROD FUNARROW
%token FUNCTION FIXPOINT LET EQUAL IN OF DOT MATCH WITH AND
%token TYPE PIPE UNDERSCORE BUILTIN EXTERNAL VALUE MAIN
%token OPENP CLOSEP OPENBRACKET CLOSEBRACKET
%token PRIME COMMA COLON SEMICOLON EOF
%token <string> FLOAT INTEGER CHAR IDENT CONSTRUCTOR

%type <Ast.expr> term

%start program
%type <Ast.program> program


%%
(*ftg:*)
(*| CHAR*)
(*| DOT { () }*)
(*;*)

(* ------------- Program ------------- *)

program:
| values EOF { { program_decls = []; main = $1 } }
| decls values EOF  { { program_decls = $1; main = $2 } }
;

(*program:
| decls values EOF { { program_decls = $1; main = $2 } }
;*)

decls:
| decl SEMICOLON { [$1] }
| decl SEMICOLON error {
    let startpos = $startpos in
    let endpos   = $endpos in
    let scurr    = startpos.Lexing.pos_cnum in
    let ecurr    = endpos.Lexing.pos_cnum in
      failwith (Printf.sprintf "syntax error between characters %d and %d" scurr ecurr)
  }
| decl SEMICOLON decls { $1 :: $3 }
;

decl:
| typedefs 
  { { Ast.item_desc = Ast.Itypedecl $1; uid = 0 } }
| EXTERNAL IDENT COLON typ 
  { { Ast.item_desc = Ast.Iexternal { external_ident = $2; external_type = $4 }; uid = 0 } };


(* -------------- Types -------------- *)

type_var:
  | PRIME IDENT { Terms.TermVar($2) }
;

type_terminal:
  | type_var { $1 }
  | IDENT    {
        match $1 with
        | "string" -> Ast.T.Predefined.string ()
        | "float" -> Ast.T.Predefined.float ()
        | "int"   -> Ast.T.Predefined.int ()
        | "char"   -> Ast.T.Predefined.char ()
        | "bool"   -> Ast.T.Predefined.bool ()
        | "unit"   -> Ast.T.Predefined.unit ()
        | _ -> Ast.T.make_userdef $1 []
      }
;

type_safe:
  | type_terminal    { $1 }
  | OPENP typ CLOSEP { $2 }
;

arrowtype:
  | type_safe TYPEARROW arrowtype  
      { Ast.T.Predefined.arrow $1 $3 }
  | type_safe TYPEARROW type_safe  
      { Ast.T.Predefined.arrow $1 $3 }
;

type_prod:
   | type_safe TYPEPROD type_prod { $1 :: $3 }
   | type_safe TYPEPROD type_safe { [$1; $3] }
;

tupletype:
  | type_prod { Ast.T.Predefined.tuple $1 }
;

type_args:
  | type_safe COMMA type_safe   { [$1; $3] }
  | type_safe COMMA type_args 
      { $1 :: $3 }
;

type_app:
  | IDENT type_safe 
      { Ast.T.make_userdef $1 [$2] }
  | IDENT OPENP type_args CLOSEP {
        Ast.T.make_userdef $1 $3
    }
;

typ:
  | type_safe { $1 }
  | arrowtype { $1 }
  | tupletype { $1 }
  | type_app  { $1 }
;

cons_def:
  | CONSTRUCTOR { ($1, None) }
  | CONSTRUCTOR OF typ { ($1, (Some $3)) }
;

adt_def:
  | cons_def { [$1] }
  | cons_def PIPE adt_def { $1 :: $3 }
;

type_kind:
  | OPENBRACKET adt_def CLOSEBRACKET { $2 }
;

typedef_args_list:
  | PRIME IDENT { [$2] }
  | PRIME IDENT COMMA typedef_args_list { $2 :: $4 }
;

typedef_args:
  | PRIME IDENT    { [ $2 ] }
  | OPENP typedef_args_list CLOSEP { $2 }
;

typedefs:
  | TYPE typedef_list { $2 }
;

typedef_list:
  | typedef { [$1] }
  | typedef AND typedef_list { $1 :: $3 }
;

typedef:
  | IDENT EQUAL BUILTIN
      { { Ast.tdecl_name       = $1;
          Ast.tdecl_kind       = Ast.Builtin } }
  | IDENT EQUAL type_kind
      { { Ast.tdecl_name       = $1;
          Ast.tdecl_kind       = Ast.SumType (Ast.IndIntros { ind_intros = $3 }) } }
  | IDENT typedef_args EQUAL type_kind
      { 
	let inductive_def = List.fold_right (fun var body ->
	  Ast.IndAbs { ind_type_var = var; ind_type = body }
	) $2 (Ast.IndIntros { ind_intros = $4 }) in
	{ Ast.tdecl_name       = $1;
          Ast.tdecl_kind       = Ast.SumType inductive_def } }
;

(* ----------- Value list ----------- *)

values:
  | MAIN EQUAL term { $3 }
  | VALUE IDENT EQUAL term SEMICOLON values
      { Ast.mklet $2 $4 $6 }
;

(* ----------- Expressions ----------- *)


terminal:
  | IDENT { Ast.mkident $1 }
  | constant_expr { $1 }
;

constant:
  | INTEGER { (Ast.CInt (int_of_string $1)) }
  | FLOAT { (Ast.CFloat (float_of_string $1)) }
;

constant_expr:
  | constant { Ast.mkconst $1 }
;

safe:
  | terminal { $1 }
  | tuple    { $1 }
  | OPENP term CLOSEP { $2 }
;

func:
  | FUNCTION IDENT FUNARROW term { Ast.mkfun $2 $4 }
;

fixp:
  | FIXPOINT IDENT IDENT FUNARROW term { Ast.mkfix $2 $3 $5 }
;

apply:
  | safe CONSTRUCTOR { Ast.mkapp $1 (Ast.mkconstruct $2 None) }
  | apply CONSTRUCTOR { Ast.mkapp $1 (Ast.mkconstruct $2 None) }
  | safe safe  { Ast.mkapp $1 $2 }
  | apply safe { Ast.mkapp $1 $2 }
;

letbinding:
  | LET IDENT EQUAL term IN term { Ast.mklet $2 $4 $6 }
;

termlist:
  | term COMMA termlist { $1 :: $3 }
  | term COMMA term { [$1; $3] }
;

tuple:
  | OPENP termlist CLOSEP { Ast.mktuple $2 }
;

construct:
  | CONSTRUCTOR             { Ast.mkconstruct $1 None }
  | CONSTRUCTOR CONSTRUCTOR { Ast.mkconstruct $1 (Some (Ast.mkconstruct $2 None)) }
  | CONSTRUCTOR safe        { Ast.mkconstruct $1 (Some $2) }
;

patternlist:
  | pattern COMMA patternlist { $1 :: $3 }
  | pattern COMMA pattern { [$1; $3] }
;

safe_pattern:
  | IDENT       { Ast.mkpvar $1 }
  | UNDERSCORE  { Ast.mkpany }
  | CONSTRUCTOR { Ast.mkpconstruct $1 None }
  | constant    { Ast.mkpconst $1 }
  | OPENP patternlist CLOSEP { Ast.mkptuple $2 }
  | OPENP pattern CLOSEP { $2 }
;

pattern:
  | safe_pattern             { $1 }
  | CONSTRUCTOR safe_pattern { Ast.mkpconstruct $1 (Some $2) }
;

(* TODO char constants, matchable patterns *)

match_line:
  | pattern FUNARROW term { { rpatt = $1; rexpr = $3 } }
;

match_cases:
  | match_line { [$1] }
  | match_line PIPE match_cases { $1 :: $3 }
;

matching:
  | OPENBRACKET match_cases CLOSEBRACKET { $2 }
;

matchwith:
  | MATCH term WITH matching { Ast.mkmatch $2 $4 }
;  

term:
  | safe { $1 }
  | func { $1 }
  | fixp { $1 }
(*  | tuple { $1 } *)
  | construct { $1 }
  | apply { $1 }
  | matchwith { $1 }
  | letbinding { $1 }
;

%%
