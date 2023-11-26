{
open Bexp_parser
open Lexing

exception SyntaxError of string
}

let var_id = ['a'-'z' 'A' - 'Z'] ['a'-'z' 'A' - 'Z' '0' - '9' '_']*

let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read =
    parse
        | whitespace { read lexbuf }
        | newline { new_line lexbuf; read lexbuf}
        | "&&" { AND }
        | "||" { OR }
        | '(' { LEFT_PAREN }
        | ')' { RIGHT_PAREN }
        | var_id { PROP_VAR ( Lexing.lexeme lexbuf) }
        | '~' { NOT }
        | eof { EOF }
        | '=' { EQUAL }
        | ',' { COMMA }
