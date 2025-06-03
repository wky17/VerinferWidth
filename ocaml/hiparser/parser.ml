open FirrtlParser

let hiparse file =
  let lexbuf = Lexing.from_channel (open_in file) in
  FirrtlParser.file FirrtlLexer.token lexbuf
