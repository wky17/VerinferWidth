open MlirParser

let mlirparse file =
  let lexbuf = Lexing.from_channel (open_in file) in
  MlirParser.file MlirLexer.token lexbuf
