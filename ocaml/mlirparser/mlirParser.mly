%{
    open Mast

%}

%token<string> NUMERAL SYMBOL SYMBOL_
%token BRA_OPEN BRA_CLOSE PAR_OPEN PAR_CLOSE ANG_OPEN ANG_CLOSE SQR_OPEN SQR_CLOSE QUOT SPRT KEYWORD ATTRIBUTES AT EXCLAM FIRRTLDOT
%token CIRCUIT STM_MODULE PRIVATE STM_INPUT STM_OUTPUT
%token STM_NODE STM_NASS STM_INST STM_WIRE STM_REG STM_REGRESET0 UINT SINT ASYNC RESET VECTOR BUNDLE FLIP CLOCK 
%token EOF

%start file
%type <Mast.file> file

%%

file
  : circuit EOF                          { $1 }
;

circuit
  : cct fmodules                      { Fcircuit ($1, $2)}
  ;

cct
  : FIRRTLDOT CIRCUIT QUOT symbol0 QUOT BRA_OPEN               { $4 }
  ;
    
fmodules
  :                                      { [] }
  | fmodule fmodules                     { $1::$2}
  ;
    
fmodule
  : mdl ports PAR_CLOSE ATTRIBUTES BRA_OPEN statements                { FInmod ($1, $2, $6) }
  | mdl ports PAR_CLOSE BRA_OPEN statements                { FInmod ($1, $2, $5) }
  ;

mdl 
  : FIRRTLDOT STM_MODULE PRIVATE AT symbol0 PAR_OPEN            { $5 }
  | FIRRTLDOT STM_MODULE AT symbol0 PAR_OPEN            { $4 }
  ;

ports
  :                                      { [] }
  | port                           { [$1] }
  | port SPRT ports                           { $1::$3 }
  ;    

port
  : STM_INPUT symbol KEYWORD EXCLAM FIRRTLDOT typ_def
                                         { Finput ($2, $6) }
  | STM_OUTPUT symbol KEYWORD EXCLAM FIRRTLDOT typ_def
                                         { Foutput ($2, $6) }
;

ports_inst
  :                                      { [] }
  | port_inst                           { [$1] }
  | port_inst SPRT ports_inst                           { $1::$3 }
  ;    

port_inst
  : STM_INPUT symbol0 KEYWORD EXCLAM FIRRTLDOT typ_def
                                         { Finput ($2, $6) }
  | STM_OUTPUT symbol0 KEYWORD EXCLAM FIRRTLDOT typ_def
                                         { Foutput ($2, $6) }
;

btyp_def
  :                                      { Fnil }
  | symbol0 FLIP KEYWORD typ_def          { Fflips ($1, Flipped, $4, Fnil) }
  | symbol0 KEYWORD typ_def               { Fflips ($1, Nflip, $3, Fnil) }
  | symbol0 FLIP KEYWORD typ_def SPRT btyp_def 
                                         { Fflips ($1, Flipped, $4, $6) }
  | symbol0 KEYWORD typ_def SPRT btyp_def      
                                         { Fflips ($1, Nflip, $3, $5) }
;

typ_def
  : UINT ANG_OPEN numeral ANG_CLOSE      { Gtyp (Fuint $3) }
  | SINT ANG_OPEN numeral ANG_CLOSE      { Gtyp (Fsint $3) }
  | CLOCK                                { Gtyp Fclock }
  | RESET                                { Gtyp Freset}
  | ASYNC                                { Gtyp Fasyncreset}
  | UINT                                 { Gtyp (Fuint_implicit 0) }
  | SINT                                 { Gtyp (Fsint_implicit 0) }
  | VECTOR ANG_OPEN typ_def SPRT numeral ANG_CLOSE   { Atyp ($3, $5) }
  | BUNDLE ANG_OPEN btyp_def ANG_CLOSE          { Btyp ($3) }
;

/* statement */

statements
  :                                      { Qnil }
  | statement statements                 { Qcons ($1, $2) }
  ;    

statement
  : symbol STM_NASS FIRRTLDOT STM_WIRE KEYWORD EXCLAM FIRRTLDOT typ_def
                                         { Swire ($1, $8) }
  | symbol STM_NASS FIRRTLDOT STM_NODE symbol KEYWORD EXCLAM FIRRTLDOT typ_def
                                         { Snode ($1, $9) }
  | symbol STM_NASS FIRRTLDOT STM_REG symbol KEYWORD EXCLAM FIRRTLDOT typ_def SPRT
      EXCLAM FIRRTLDOT typ_def
                                         { Sreg ($1, $13) }
  | symbol STM_NASS FIRRTLDOT STM_REGRESET0 symbol SPRT symbol SPRT symbol KEYWORD EXCLAM FIRRTLDOT typ_def SPRT
      EXCLAM FIRRTLDOT typ_def SPRT EXCLAM FIRRTLDOT typ_def SPRT EXCLAM FIRRTLDOT typ_def
                                         { Sreg ($1, $25) }
  | symbols STM_NASS FIRRTLDOT STM_INST symbol0 AT symbol0 PAR_OPEN ports_inst PAR_CLOSE    { Sinst ($5, $7) }
;

/* Symbols */

symbol
  : SYMBOL                              { $1 }
;

symbol0
  : SYMBOL_                              { $1 }
;

symbols
  :                                      { [] }
  | symbol                               { [$1] }
  | symbol SPRT symbols                       { $1::$3 }
;

/* spec_constant */

numeral
  : NUMERAL                             { Stdlib.int_of_string $1 }
;
