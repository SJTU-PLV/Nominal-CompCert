//
// Created by 徐翔哲 on 12/02/2020.
//
#include "visitor.hh"
#include "ast.hh"

namespace ast {
    SingleSemiConstraint::DummyConstraint *SingleSemiConstraint::dummy
            = new SingleSemiConstraint::DummyConstraint;

    void SingleSemiConstraint::accept(ASTVisitor &visitor) {
        visitor.visit(*this);
    }


    void ASTNode::accept(ASTVisitor &visitor) {
        visitor.visit(*this);
    }

    void ConjConstraint::accept(ASTVisitor &visitor) {
        if (visitor.visit(*this)) {
            this->lhs.accept(visitor);
            this->rhs.accept(visitor);
        }
    }

    void SemiConstraint::accept(ASTVisitor &visitor) {
        if (visitor.visit(*this)) {
            this->lhs.accept(visitor);
            this->rhs.accept(visitor);
        }
    }

    void EQConstraint::accept(ASTVisitor &visitor) {
        if (visitor.visit(*this)) {
            this->lhs.accept(visitor);
            this->rhs.accept(visitor);
        }
    }

    void NEConstraint::accept(ASTVisitor &visitor) {
        if (visitor.visit(*this)) {
            this->lhs.accept(visitor);
            this->rhs.accept(visitor);
        }
    }

    void ParamList::accept(ASTVisitor &visitor) {
        if (visitor.visit(*this)) {
            for (auto p:params) {
                p->accept(visitor);
            }
        }
    }

    void UType::accept(ASTVisitor &visitor) {
        if (visitor.visit(*this)) {
            this->cons.accept(visitor);
            this->paramList.accept(visitor);
        }
    }

    void Instruction::accept(ASTVisitor &visitor) {
        if (visitor.visit(*this)) {
            this->cons.accept(visitor);
            this->paramList.accept(visitor);
        }
    }

    void Specification::accept(ASTVisitor &visitor) {
        if (visitor.visit(*this)) {
            for (auto p:this->tops) {
                p->accept(visitor);
            }
        }

    }

    void Name::accept(ASTVisitor &visitor) {
        visitor.visit(*this);
    }

    void Num::accept(ASTVisitor &visitor) {
        visitor.visit(*this);

    }

    void Token::accept(ASTVisitor &visitor) {
        visitor.visit(*this);
    }

    void Field::accept(ASTVisitor &visitor) {
        visitor.visit(*this);
    }

    void ConstraintBase::ConstRef::accept(ASTVisitor &visitor) {
        visitor.visit(*this);

    }

    void ConstraintBase::NameRef::accept(ASTVisitor &visitor) {
        visitor.visit(*this);

    }

    void NamedConstraint::accept(ASTVisitor &visitor) {
        visitor.visit(*this);

    }

    void Param::accept(ASTVisitor &visitor) {
        visitor.visit(*this);

    }

    void ClsConstraint::accept(ASTVisitor &visitor) {
        visitor.visit(*this);
    }

    void FldConstraint::accept(ASTVisitor &visitor) {
        visitor.visit(*this);
    }

    void Constructor::accept(ASTVisitor &visitor) {
        visitor.visit(*this);
    }

    void Klass::accept(ASTVisitor &visitor) {
        visitor.visit(*this);
    }
}
