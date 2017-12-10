{
  open Parser
}

let digit = ['0'-'9']
let letter = ['a'-'z'] | ['A'-'Z']
let upper_case_letter = ['A'-'Z']
let lower_case_letter = ['a'-'z']

rule token = parse
  | [' ' '\t'] { token lexbuf }
  | digit+ as num { INTEGER(num) }
  | "." digit+
  | digit+ "." digit* as num
      { FLOAT (num) }
  | "builtin" { BUILTIN }
  | "external" { EXTERNAL }
  | "value" { VALUE }
  | "main" { MAIN }
  | "let" { LET }
  | "in" { IN }
  | "and" { AND }
  | "of" { OF }
  | "fun" { FUNCTION }
  | "fix" { FIXPOINT }
  | "="   { EQUAL }
  | "match" { MATCH }
  | "with" { WITH }
  | "type" { TYPE }
  | "|" { PIPE }
  | "_" { UNDERSCORE }
  | "(" { OPENP }
  | ")" { CLOSEP }
  | "[" { OPENBRACKET }
  | "]" { CLOSEBRACKET }  
  | '\'' { PRIME }
  | ',' { COMMA }
  | '.' { DOT }
  | ':' { COLON }
  | ';' { SEMICOLON }
  | "=>" { FUNARROW }
  | "->" { TYPEARROW }
  | "*"  { TYPEPROD }
  | (upper_case_letter)(letter | digit | '_' | '\'')*  as id { CONSTRUCTOR(id) }
  | (lower_case_letter | '_')(letter | digit | '_' | '\'')*  as id { IDENT(id) }
  | _ { token lexbuf }
  | eof { EOF }
