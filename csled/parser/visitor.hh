//
// Created by 徐翔哲 on 12/02/2020.
//

#ifndef FRONTEND_VISITOR_HH
#define FRONTEND_VISITOR_HH

#include "ast.hh"

namespace ast {

    class ASTVisitor {
    public:
        virtual bool visit(ASTNode &node) = 0;

        virtual bool visit(TopDef &node) = 0;

        virtual bool visit(Name &node) = 0;

        virtual bool visit(Num &node) = 0;

        virtual bool visit(Token &node) = 0;

        virtual bool visit(Field &node) = 0;

        virtual bool visit(ConstraintBase &node) = 0;

        virtual bool visit(ConstraintBase::ConstraintRef &node) = 0;

        virtual bool visit(ConstraintBase::NameRef &node) = 0;

        virtual bool visit(ConstraintBase::ConstRef &node) = 0;

        virtual bool visit(ConjConstraint &node) = 0;

        virtual bool visit(SemiConstraint &node) = 0;

        virtual bool visit(EQConstraint &node) = 0;

        virtual bool visit(NEConstraint &node) = 0;

        virtual bool visit(NamedConstraint &node) = 0;

        virtual bool visit(Param &node) = 0;

        virtual bool visit(ParamList &node) = 0;

        virtual bool visit(UType &node) = 0;

        virtual bool visit(Instruction &node) = 0;

        virtual bool visit(Specification &node) = 0;

        //new ast nodes
        virtual bool visit(SingleSemiConstraint &node) = 0;

        virtual bool visit(ClsConstraint &node) = 0;

        virtual bool visit(FldConstraint &node) = 0;

        virtual bool visit(Constructor &node) = 0;

        virtual bool visit(Klass &node) = 0;


    };
}

#endif //FRONTEND_VISITOR_HH
