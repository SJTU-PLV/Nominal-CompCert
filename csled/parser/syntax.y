%{
#include<iostream>
#include"parser/ast.hh"
#include"syntax.tab.hh"
#include"parser/common.hh"


using namespace ast;

Specification* root=nullptr;
%}

%require "3.6"
%language "c++"
%locations
%define api.token.constructor
%define api.value.type variant
%define api.token.prefix {TOK_}
%define parse.trace
%define parse.error detailed
%define parse.lac full

%token <int> NUMBER
%token <std::string> STRING 
%token <std::string> LS RS LB RB SEMI CONJ COLO COMMA BAR LP RP
%token <std::string> EQ NE
%token <std::string> TOKEN FIELD KLASS CONSTR CLZ FLD PCT

%nterm <ast::Name*> name
%nterm <ast::Num*> num

%nterm <ast::Specification*> topList
%nterm <ast::TopDef*> top
%nterm <ast::Token*> token
%nterm <ast::Field*> field
%nterm <ast::Klass*> klass
%nterm <vector<ast::Constructor*>*> KDefList
%nterm <ast::Constructor*> KDef
%nterm <vector<string>*> args
%nterm <ast::Name*> arg
%nterm <ast::SemiConstraint*> patterns
%nterm <ast::ConstraintBase*> constraint


// %nterm <ast::Instruction*> instruction
// %nterm <ast::UType*> utype
// %nterm <ast::ConstraintBase*> constraint
// %nterm <ast::ParamList*> paramList paramTail
// %nterm <ast::Param*> param

%left SEMI
%left CONJ

%%
topList:
%empty{
    $$ = new ast::Specification;
    root = $$;
}
|top topList
{
    $2->addTopDef($1);
    $$ = $2;
    root = $$;
}
;


top: 
token SEMI{
    $$ = $1;
}
|field SEMI{ 
    $$ = $1;
}
|klass SEMI{
    $$ = $1;
}
;

token: 
TOKEN name EQ LP num RP{
    $$ = new Token($2->name,$5->num);
    delete $2;
    delete $5;
}
;

name: 
STRING{
    $$ = new Name($1);
}
;

num: 
NUMBER{
    $$ = new Num($1);
}
;

field: 
FIELD name EQ name LP num COLO num RP{
    $$ = new Field($2->name, $4->name, $6->num, $8->num);
    delete $2;
    delete $4;
    delete $6;
    delete $8;
}
;

klass:
KLASS name EQ KDefList{
    $$ = new Klass($2->name, *$4);
    delete $2;
}
;

KDefList:
BAR KDef KDefList{
    $3->push_back($2);
    $$ = $3;
}
|BAR KDef{
    $$ = new vector<Constructor*>;
    $$->push_back($2);
}
;

KDef:
CONSTR name LS args RS LP patterns RP{
    $$ = new Constructor($2->name, *$4, *$7);
    delete $2;
}
;

args:
arg{
    $$ = new vector<string>;
    if($1 != nullptr){
        $$->push_back($1->name);
        delete $1;
    }
}
|args COMMA arg{
    $1->push_back($3->name);
    $$ = $1;
    delete $3;
}
;

arg:
name{
    $$ = $1;
}
|%empty{
    $$ = nullptr;
}
;

patterns:
constraint{
    $$ = new SingleSemiConstraint(*$1);
}
| constraint SEMI patterns{
    $$ = new SemiConstraint(*$1, *$3);
}
;

constraint: 
constraint CONJ constraint{
    $$ = new ConjConstraint(*$1, *$3);
}
|name EQ num{
    auto lhs = new ConstraintBase::NameRef($1->name);
    auto rhs = new ConstraintBase::ConstRef($3->num);
    $$ = new EQConstraint(*lhs,*rhs);
    delete $1;
    delete $3;
}
|name NE num{
    auto lhs = new ConstraintBase::NameRef($1->name);
    auto rhs = new ConstraintBase::ConstRef($3->num);
    $$ = new NEConstraint(*lhs,*rhs);
    delete $1;
    delete $3;
}
|FLD PCT num{
    $$ = new FldConstraint($3->num);
    delete $3;
}
|CLZ PCT num{
    $$ = new ClsConstraint($3->num);
    delete $3;
}
;

%%

void yy::parser::error (const location_type& l, const std::string& m) { 
    std::cerr << l << ": " << m << std::endl; 
}