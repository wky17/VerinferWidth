{
  open MlirParser

  exception Error of string
  let lnum = ref 1
  let cnum = ref 0
  let get_len lexbuf = String.length (Lexing.lexeme lexbuf)
  let upd_cnum lexbuf = cnum := !cnum + get_len lexbuf
  let reset_cnum () = cnum := 0
}

let digit = ['0'-'9']
let numeral = '0' | ['1'-'9'] digit*
let letter = ['a'-'z' 'A'-'Z' '_' '-']
let symbol0 = ('|' [^'|']+ '|') | (letter|'_'|digit)*
let escape_space = "\"\""

rule line_comment = parse
 ("\r\n"|'\n'|'\r')                     { reset_cnum(); incr lnum; token lexbuf }
| _                                     { upd_cnum lexbuf; line_comment lexbuf }
                                   
and token = parse

| [' ' '\t']                            { upd_cnum lexbuf; token lexbuf }
| ("\r\n"|'\n'|'\r')                    { reset_cnum(); incr lnum; token lexbuf }
| "attributes {convention = #firrtl<convention scalarized>}"
                                        { upd_cnum lexbuf; ATTRIBUTES }
| '('                                   { upd_cnum lexbuf; PAR_OPEN }
| ')'                                   { upd_cnum lexbuf; PAR_CLOSE }
| '<'                                   { upd_cnum lexbuf; ANG_OPEN }
| '>'                                   { upd_cnum lexbuf; ANG_CLOSE }
| '['                                   { upd_cnum lexbuf; SQR_OPEN }
| ']'                                   { upd_cnum lexbuf; SQR_CLOSE }
| '{'                                   { upd_cnum lexbuf; BRA_OPEN }
| '}'                                   { upd_cnum lexbuf; BRA_CLOSE }
| '"'                                   { upd_cnum lexbuf; QUOT } 
| '@'                                   { upd_cnum lexbuf; AT }
| '!'                                   { upd_cnum lexbuf; EXCLAM }
| ':'                                   { upd_cnum lexbuf; KEYWORD }
| ','                                   { upd_cnum lexbuf; SPRT }
| "firrtl."                            { upd_cnum lexbuf; FIRRTLDOT }
| numeral as str                        { upd_cnum lexbuf; NUMERAL str }

| "circuit"                             { upd_cnum lexbuf; CIRCUIT }
| "module"                              { upd_cnum lexbuf; STM_MODULE }
| "private"                              { upd_cnum lexbuf; PRIVATE }
| "in"                                  { upd_cnum lexbuf; STM_INPUT }
| "out"                                 { upd_cnum lexbuf; STM_OUTPUT }

| "wire"                                { upd_cnum lexbuf; STM_WIRE }
| "reg"                                 { upd_cnum lexbuf; STM_REG }
| "regreset"                            { upd_cnum lexbuf; STM_REGRESET0 }
| "node"                                { upd_cnum lexbuf; STM_NODE }
| "="                                   { upd_cnum lexbuf; STM_NASS }
| "instance"                                { upd_cnum lexbuf; STM_INST }

(* Types *)
| "uint"                                { upd_cnum lexbuf; UINT }
| "sint"                                { upd_cnum lexbuf; SINT }
| "clock"                               { upd_cnum lexbuf; CLOCK }
| "asyncreset"                          { upd_cnum lexbuf; ASYNC }
| "reset"                               { upd_cnum lexbuf; RESET }
| "vector"                               { upd_cnum lexbuf; VECTOR }
| "bundle"                               { upd_cnum lexbuf; BUNDLE }

| "flip"                                { upd_cnum lexbuf; FLIP }
| symbol0 as str                         { upd_cnum lexbuf; SYMBOL_ str }
| "%" (symbol0 as str)                         { upd_cnum lexbuf; SYMBOL str }
| eof                                   { EOF }
