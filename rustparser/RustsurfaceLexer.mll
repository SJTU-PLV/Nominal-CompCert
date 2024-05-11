{
open RustsurfaceParser
}

let white = [' ' '\t' '\n']+
let digit = ['0' - '9']
let int = '-' ? digit+
let float = '-' ? digit+ "." digit+
let letter = ['a' - 'z' 'A' - 'Z' '_']
let letter_num = ['a' - 'z' 'A' - 'Z' '0' - '9' '_']
let id = letter ? letter_num+

rule read = 
	parse
	| white { read lexbuf }
	| int { INT (int_of_string (Lexing.lexeme lexbuf)) }

 | "+" { ADD }
 | "-" { SUBS }
 | "/" { DIV }

 | "!" { NOT }
 | "<=" { LE }
 | ">=" { GE }
 | "==" { EQ }
 | "!=" { NE }
 | "||" { OR }
 | "&&" { AND }
 | "&" { REF }

 | '"' _* '"' { let s = Lexing.lexeme lexbuf in
                STR_LITERAL (String.sub s 1 (String.length s - 2)) }

 | "=" { ASSIGN }
 | "*" { ASTERISK }
 | ":" { COLON }
 | ";" { SEMICOLON }
 | "::" { COLON2 }
 | "," { COMMA }
 | "->" { RARROW }
 | "=>" { RARROWW }
 | "." { DOT }

 | "(" { LPAREN }
 | ")" { RPAREN }
 | "<" { LANGLE }
 | ">" { RANGLE }
 | "{" { LBRACE }
 | "}" { RBRACE}

 | "i8" { INT8 }
 | "u8" { UINT8 }
 | "i16" { INT16 }
 | "u16" { UINT16 }
 | "i32" { INT32 }
 | "u32" { UINT32 }
 | "i64" { INT64 }
 | "u64" { UINT64 }

 | "f32" { FLOAT32 }
 | "f64" { FLOAT64 }

 | "bool" { BOOL }
 | "true" { TRUE }
 | "false" { FALSE }

 | "struct" { STRUCT }
 | "enum" { ENUM }

 | "fn" { FN }
 | "in" { IN }
 | "let" { LET }

 | "loop" { LOOP }
 | "while" { WHILE }
 | "if" { IF }
 | "else" { ELSE }
 | "continue" { CONTINUE }
 | "break" { BREAK }

 | "return" { RETURN }
 | "Box" { BOX }
 | "match" { MATCH }
 | "case" { CASE }
 | "as" { AS }
 | "mut" { MUT }

 | id { ID (Lexing.lexeme lexbuf) }
 | eof { EOF }

 | _ as c { failwith (Printf.sprintf "unexpected character: %C" c) }
