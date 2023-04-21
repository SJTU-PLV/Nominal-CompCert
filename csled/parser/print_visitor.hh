//
// Created by 徐翔哲 on 12/02/2020.
//

#ifndef FRONTEND_PRINT_VISITOR_HH
#define FRONTEND_PRINT_VISITOR_HH
#include "visitor.hh"
#include "ast.hh"
#include <iostream>
namespace ast {
    class PrintVisitor : public ASTVisitor {
    private:
        int identCounter = 0;
        void printIdent(){
            for (int i = 0; i < identCounter; i++) {
                std::cout << "  ";
            }
        }
    public:
        bool visit(ASTNode &node) override;

        bool visit(TopDef &node) override;

        bool visit(Name &node) override;

        bool visit(Num &node) override;

        bool visit(Token &node) override;

        bool visit(Field &node) override;

        bool visit(ConstraintBase &node) override;

        bool visit(ConstraintBase::ConstraintRef &node) override;

        bool visit(ConstraintBase::NameRef &node) override;

        bool visit(ConstraintBase::ConstRef &node) override;

        bool visit(ConjConstraint &node) override;

        bool visit(SemiConstraint &node) override;

        bool visit(EQConstraint &node) override;

        bool visit(NEConstraint &node) override;

        bool visit(NamedConstraint &node) override;

        bool visit(Param &node) override;

        bool visit(ParamList &node) override;

        bool visit(UType &node) override;

        bool visit(Instruction &node) override;

        bool visit(Specification &node) override;

        bool visit(SingleSemiConstraint &node) override;

        bool visit(ClsConstraint &node) override;

        bool visit(FldConstraint &node) override;

        bool visit(Constructor &node) override;

        bool visit(Klass &node) override;
    };
}

#endif //FRONTEND_PRINT_VISITOR_HH
