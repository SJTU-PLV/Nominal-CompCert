
#ifndef ARTIFACT_COQGEN_HH
#define ARTIFACT_COQGEN_HH


#include <string>
#include <iostream>
#include <vector>
#include "../ir/ir.hh"
#include <sstream>
//#include "encoder.hh"
//#include "consistence.hh"
using namespace std;

namespace coq {
    struct Parameter {
        string name;
        string type;

        Parameter(const string &name, const string &type)
                : name(name), type(type) {}

        Parameter() = default;

        virtual string toString() {
            if (type.empty()) {
                return name;
            } else {
                return "(" + name + ":" + type + ")";
            }
        }
    };

    struct InductiveArm {
        string constructorName;
        vector<Parameter *> params;

        virtual string toString() {
            stringstream ret;
            ret << constructorName;
            for (auto p: params) {
                ret << p->toString();
            }
            return ret.str();
        }
    };

    struct InductiveType {
        string typeName;
        vector<InductiveArm *> constructors;

        virtual string toString();
    };


    struct Statement {
        string anything;

        Statement() {}

        Statement(const string &anything) : anything(anything) {}

        virtual ~Statement() = default;

        virtual string toString();
    };

    struct IfThenElse : public Statement {
        string condition;
        vector<Statement *> thenStmts;
        vector<Statement *> elseStmts;

        string toString() override;

        virtual ~IfThenElse();
    };

    struct ErrorStmt : public Statement {
        string msg;

        ErrorStmt(const string &msg) : msg(msg) {}

        ErrorStmt() = default;

        string toString() override;
    };

    struct MatchArm : public Statement {
        string constructor;
        vector<string> params;
        vector<Statement *> stmts;

        string toString() override;

        virtual ~MatchArm();
    };

    struct MatchStatement : public Statement {
        string variable;
        vector<MatchArm *> branches;

        string toString() override;

        ~MatchStatement();

    };

    struct DoStatement : public Statement {
        string bind;
        string expr;

        string toString() override;
    };

    struct LetStatement : public Statement {
        string bind;
        string expr;

        LetStatement() = default;

        LetStatement(const string &bind, const string &expr)
                : bind(bind), expr(expr) {}

        string toString() override;
    };

    struct Expression {
        string anything;

        Expression() {}

        Expression(const string &anything) : anything(anything) {}

        virtual string toString() { return anything; }
    };

    struct ListFirstN : public Expression {
        string list;
        int n;

        ListFirstN(const string &list, int n)
                : list(list), n(n) {}

        string toString() override {
            return list + "~@[" + to_string(n) + "]";
        }
    };

    struct ListSkipN : public Expression {
        string list;
        int n;

        ListSkipN(const string &list, int n)
                : list(list), n(n) {}

        string toString() override {
            return list + ">@[" + to_string(n) + "]";
        }
    };

    struct BitsToByte : public Expression {
        string bits;

        BitsToByte(const string &bits)
                : bits(bits) {}

        string toString() override {
            return "bB[" + bits + "]";
        }
    };

    struct ParenthesisExpression : public Expression {
        string expression;

        ParenthesisExpression(const string &expression)
                : expression(expression) {}

        string toString() override {
            return "(" + expression + ")";
        }
    };

    struct BuiltInConstructor : public Expression {
        string varName;
        string evidence;
        int width;
        BuiltInConstructor(const string &varName, const string &evidence, int width)
                : varName(varName), evidence(evidence), width(width) {}

        string toString();

    };

    struct Definition {
        string name;
        vector<Parameter *> params;
        string retValue;
        vector<Statement *> body;

        virtual string toString();
    };

    struct ProgramDefinition:public Definition{
        virtual string toString();
    };

    struct Lemma {
        string name;
        string body;
        string proof;

        virtual string toString() {
            stringstream ret;
            ret << "Lemma " << name << ": " << endl
                << body << endl
                << "Proof." << endl
                << proof << endl;
            return ret.str();
        }
    };

    struct Axiom {
        string name;
        string body;

        virtual string toString(){
            stringstream ret;
            ret << "Axiom "<< name <<": "<<endl
            <<body <<endl;
            return ret.str();
        }
    };

    class CoqPrinter {
        const map<string, ir::BitField *> &nameBFMap;
        const map<string, ir::UType *> &irNameUTypeMap;
        const map<string, ir::Instruction *> &irNameInstrMap;
        stringstream sout;
        stringstream encproof;//enc_consistency
        stringstream decproof;//dec_consistency
        stringstream bftrue;
        void generateString();

        void generateFixLength();

        void generateInstrBp();

        void generateUTypeBp();

        void generateEncDec();

        void generateListProof();

        void generate_Enc_Consistency();

        void generate_Dec_Consistency();

        void generate_BFtrue();

        void generateBpHintdb();
    public:
        CoqPrinter(const map<string, ir::BitField *> &nameBfMap, const map<string, ir::UType *> &irNameUTypeMap,
                   const map<string, ir::Instruction *> &irNameInstrMap)
                : nameBFMap(nameBfMap), irNameUTypeMap(irNameUTypeMap), irNameInstrMap(irNameInstrMap) {}

        string print() {
            generateString();
            return sout.str();
        }

        string enc_consistency_print(){
            generate_Enc_Consistency();
            return encproof.str();
        }

        string dec_consistency_print(){
            generate_Dec_Consistency();
            return decproof.str();
        }

        string bf_true_print(){
            generate_BFtrue();
            return bftrue.str();
        }
    };
}


#endif //ARTIFACT_COQGEN_HH
