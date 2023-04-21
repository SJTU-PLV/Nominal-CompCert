#ifndef SSLED_AST
#define SSLED_AST

#include <string>
#include <vector>
#include <set>
#include <cassert>

using namespace std;


namespace ast {
    class ASTVisitor;

    class ASTNode {
    protected:
        ASTNode() = default;

    public:
        virtual void accept(ASTVisitor &visitor) = 0;

        ASTNode(ASTNode &) = default;

        ASTNode(ASTNode &&) = default;

        ASTNode &operator=(ASTNode &&) = default;

        virtual ~ASTNode() = default;
    };


    class TopDef : public ASTNode {
    };

    class Name : public ASTNode {
    public:
        Name() = default;

        string name;

        Name(const string &name) : name(name) {}

        const string &getName() const {
            return name;
        }

        void accept(ASTVisitor &visitor) override;

    };

    class Num : public ASTNode {
    public:
        Num() = default;

        int num;

        Num(int &number) : num(number) {}

        int getNum() const {
            return num;
        }

        void accept(ASTVisitor &visitor) override;

    };

    class Token : public TopDef {
        string tokenName;
        int tokenWidth;
    public:
        Token() = default;

        Token(const string &tokenName, int tokenWidth)
                : tokenName(tokenName), tokenWidth(tokenWidth) {}

        void accept(ASTVisitor &visitor) override;

        const string &getTokenName() const {
            return tokenName;
        }

        int getTokenWidth() const {
            return tokenWidth;
        }
    };

    class Field : public TopDef {
        string fieldName;
        string tokenName;
        int bfBegin, bfEnd;
    public:
        Field() = default;

        Field(const string &fn, const string &tn, int bb, int be)
                : fieldName(fn), tokenName(tn), bfBegin(bb), bfEnd(be) {}

        void accept(ASTVisitor &visitor) override;

        const string &getFieldName() const {
            return fieldName;
        }

        const string &getTokenName() const {
            return tokenName;
        }

        int getBfBegin() const {
            return bfBegin;
        }

        int getBfEnd() const {
            return bfEnd;
        }
    };


    class ConstraintBase : public ASTNode {
    public:

        class ConstraintRef : public ASTNode {

        };

        class NameRef : public ConstraintRef {
            string name;
        public:
            NameRef(const string &name) : name(name) {}

            void accept(ASTVisitor &visitor) override;

            const string &getName() const {
                return name;
            }
        };

        class ConstRef : public ConstraintRef {
            int number;
        public:
            ConstRef(int number) : number(number) {}

            void accept(ASTVisitor &visitor) override;

            int getNumber() const {
                return number;
            }
        };
    };

    class ConjConstraint : public ConstraintBase {
        ConstraintBase &lhs;
        ConstraintBase &rhs;
    public:
        ConjConstraint(ConstraintBase &lhs, ConstraintBase &rhs) : lhs(lhs), rhs(rhs) {}

        void accept(ASTVisitor &visitor) override;

        ConstraintBase &getLhs() const {
            return lhs;
        }

        ConstraintBase &getRhs() const {
            return rhs;
        }
    };

    class SemiConstraint : public ConstraintBase {
        ConstraintBase &lhs;
        ConstraintBase &rhs;
    public:
        SemiConstraint(ConstraintBase &lhs, ConstraintBase &rhs) : lhs(lhs), rhs(rhs) {}

        void accept(ASTVisitor &visitor) override;

        ConstraintBase &getLhs() const {
            return lhs;
        }

        ConstraintBase &getRhs() const {
            return rhs;
        }
        virtual bool isSingle(){
            return false;
        }
    };


    //FIXME: bad design
    class SingleSemiConstraint : public SemiConstraint {
        class DummyConstraint : public ConstraintBase {
            void accept(ASTVisitor &visitor) override {
                //This should never happen
                assert(false);
            }
        };

        static DummyConstraint *dummy;
    public:
        SingleSemiConstraint(ConstraintBase &lhs) : SemiConstraint(lhs, *dummy) {}

        bool isSingle() override {
            return true;
        }

        void accept(ASTVisitor &visitor) override;

    };


    class EQConstraint : public ConstraintBase {
        ConstraintRef &lhs;
        ConstraintRef &rhs;
    public:
        EQConstraint(ConstraintRef &lhs, ConstraintRef &rhs) : lhs(lhs), rhs(rhs) {}

        void accept(ASTVisitor &visitor) override;

        ConstraintRef &getLhs() const {
            return lhs;
        }

        ConstraintRef &getRhs() const {
            return rhs;
        }
    };

    class NEConstraint : public ConstraintBase {
        ConstraintRef &lhs;
        ConstraintRef &rhs;
    public:
        NEConstraint(ConstraintRef &lhs, ConstraintRef &rhs) : lhs(lhs), rhs(rhs) {}

        void accept(ASTVisitor &visitor) override;

        ConstraintRef &getLhs() const {
            return lhs;
        }

        ConstraintRef &getRhs() const {
            return rhs;
        }
    };

    //Deprecated
    class NamedConstraint : public ConstraintBase {
        string name;
    public:
        NamedConstraint(const string &name) : name(name) {}

        void accept(ASTVisitor &visitor) override;

        const string &getName() const {
            return name;
        }
    };

    class ClsConstraint : public ConstraintBase {
        int index;
    public:
        ClsConstraint(int index) : index(index) {}

        void accept(ASTVisitor &visitor) override;

        int getIndex() const {
            return index;
        }
    };

    class FldConstraint : public ConstraintBase {
        int index;
    public:
        FldConstraint(int index) : index(index) {}

        void accept(ASTVisitor &visitor) override;

        int getIndex() const {
            return index;
        }
    };

    class Param : public ASTNode {
        string name;
        string typeName;
    public:
        Param(const string &name, const string &typeName) : name(name), typeName(typeName) {}

        void accept(ASTVisitor &visitor) override;

        const string &getName() const {
            return name;
        }

        const string &getTypeName() const {
            return typeName;
        }
    };

    class ParamList : public ASTNode {
        vector<Param *> &params;
    public:
        ParamList() : params(*new vector<Param *>) {}

        ParamList(const ParamList &) = delete;


        ParamList &operator=(const ParamList &) = delete;

        ~ParamList() override {
            delete &params;
        }

        void accept(ASTVisitor &visitor) override;

        void addParam(Param *param) {
            params.push_back(param);
        }

        vector<Param *> &getParams() const {
            return params;
        }


    };

    //Deprecated
    class UType : public TopDef {
        string typeName;
        ConstraintBase &cons;
        ParamList &paramList;
    public:
        UType(const string &typeName, ConstraintBase &cons, ParamList &paramList)
                : typeName(typeName), cons(cons), paramList(paramList) {}

        void accept(ASTVisitor &visitor) override;

        const string &getTypeName() const {
            return typeName;
        }

        ConstraintBase &getCons() const {
            return cons;
        }

        ParamList &getParamList() const {
            return paramList;
        }
    };

    //Deprecated
    class Instruction : public TopDef {
        string instrName;
        ConstraintBase &cons;
        ParamList &paramList;
    public:
        Instruction(const string &instrName, ConstraintBase &cons, ParamList &paramList)
                : instrName(instrName), cons(cons), paramList(paramList) {}

        void accept(ASTVisitor &visitor) override;

        const string &getInstrName() const {
            return instrName;
        }

        ConstraintBase &getCons() const {
            return cons;
        }

        ParamList &getParamList() const {
            return paramList;
        }
    };

    class Constructor : public ASTNode{
        string constructorName;
        vector<string> aids;
        SemiConstraint &pattern;
    public:

        Constructor(const string &constructorName, const vector<string> &aids, SemiConstraint &pattern)
                : constructorName(constructorName), aids(aids), pattern(pattern) {}

        void accept(ASTVisitor &visitor) override;

        const string &getConstructorName() const {
            return constructorName;
        }

        const vector<string> &getAids() const {
            return aids;
        }

        SemiConstraint &getPattern() const {
            return pattern;
        }
    };

    class Klass : public TopDef {
        string klassName;
        vector<Constructor *> constructors;
    public:
        Klass() = default;

        Klass(const string &klassName, const vector<Constructor *> &constructors) : klassName(klassName),
                                                                                    constructors(constructors) {}

        const vector<Constructor *> &getConstructors() const {
            return constructors;
        }

        const string &getKlassName() const {
            return klassName;
        }

        void accept(ASTVisitor &visitor) override;

    };

    class Specification : public ASTNode {
        vector<TopDef *> &tops;
    public:
        Specification() : tops(*new vector<TopDef *>) {}

        Specification(Specification &&s) noexcept: tops(s.tops) {}

        ~Specification() override {
            delete &tops;
        }

        Specification &operator=(const Specification &) = delete;

        Specification(const Specification &) = delete;

        Specification &operator=(Specification &&s) noexcept {
            delete &tops;
            tops = s.tops;
            return *this;
        }

        void accept(ASTVisitor &visitor) override;


        void addTopDef(TopDef *def) {
            tops.push_back(def);
        }

        vector<TopDef *> &getTops() const {
            return tops;
        }


    };

}

#endif