%{
#include "parser/ast.hh"
#include "syntax.tab.hh"
#include "parser/common.hh"
#include <cstdlib>
#include <string>
#include <iostream>
#define MAKETOKEN(x) yy::parser::make_ ## x (yytext,loc)
//#define RECORD(x) printf("token type: %s\n", #x);
#define RECORD(x)

yy::parser::symbol_type make_NUMBER (const std::string&s, const yy::parser::location_type& loc){
  return yy::parser::make_NUMBER(stoi(s, 0, 0),loc);
}


yy::location loc;

#define YY_USER_ACTION \
  {\
    loc.columns(yyleng);\
  }
//printf("Lexer saw token: [%s]  ", yytext);\
%}

%option noyywrap nounput noinput batch

alpha [a-zA-Z_]
digit [0-9]
space [ \t]
hex 0x[a-fA-F0-9]+

%%

{space}+  {
  loc.step();
  RECORD(SPACE)
}

\n+ {
  loc.lines(yyleng); loc.step();
  RECORD(NEWLINE)
}
; {
    RECORD(SEMI)
    return MAKETOKEN(SEMI);
}
{digit}+|{hex} {
    RECORD(NUMBER)
    return make_NUMBER(yytext, loc);
}
\[ {
  RECORD(LS)
  return MAKETOKEN(LS);
}

\] {
  RECORD(RS)
  return MAKETOKEN(RS);
}

\{ {
  RECORD(LB)
  return MAKETOKEN(LB);
}

\} {
  RECORD(RB)
  return MAKETOKEN(RB);
}

\( {
  RECORD(LP)
  return MAKETOKEN(LP);
}

\) {
  RECORD(RP)
  return MAKETOKEN(RP);
}

% {
  RECORD(PCT)
  return MAKETOKEN(PCT);
}

& {
  RECORD(CONJ)
  return MAKETOKEN(CONJ);
}

: {
  RECORD(COLO)
  return MAKETOKEN(COLO);
}

, {
  RECORD(COMMA)
  return MAKETOKEN(COMMA);
}

\| {
  RECORD(BAR)
  return MAKETOKEN(BAR);
}
= {
  RECORD(EQ)
  return MAKETOKEN(EQ);
}

!= {
  RECORD(NE)
  return MAKETOKEN(NE);
}

token {
  RECORD(TOKEN)
  return MAKETOKEN(TOKEN);
}


field {
  RECORD(FIELD)
  return MAKETOKEN(FIELD);
}

class {
  RECORD(KLASS)
  return MAKETOKEN(KLASS);
}

constr {
  RECORD(CONSTR)
  return MAKETOKEN(CONSTR);
}

cls {
  RECORD(CLZ)
  return MAKETOKEN(CLZ);
}

fld {
  RECORD(FLD)
  return MAKETOKEN(FLD);
}

({alpha})({alpha}|{digit})* {
  RECORD(STRING)
  return MAKETOKEN(STRING);
}
\/\/[^\n]* {
  RECORD(COMMENTS)
}
. {
  RECORD(UNKNOWN)
  std::cerr<<"Lexical Error at:" << loc<<std::endl;
}
<<EOF>> {
  return yy::parser::make_YYEOF(loc);
}
%%