//
// Created by 徐翔哲 on 12/03/2020.
//

#ifndef FRONTEND_TOKEN_CHECKER_HH
#define FRONTEND_TOKEN_CHECKER_HH

#include "../parser/ast.hh"
#include "../parser/visitor.hh"
#include <map>
#include <string>
#include <vector>
#include <set>

/**
 * TokenChecker checks:
 *  1. All the names used are defined
 *  2. All the instructions, tokens, and fields are defined only once.
 * Also,
 *  3. Generating name-token, name-utype, name-instruction, and name-field maps
 */

using namespace std;

namespace preprocessor {
    class NameChecker : public ast::ASTVisitor {
    private:
        bool hasError = false;
        set<string> paramNames;


        set<string> undefinedName;
        map<string, ast::Token *> nameTokenMap;
        map<string, ast::Field *> nameFieldMap;
        map<string, ast::Instruction *> nameInstrMap;
        map<string, ast::Klass *> nameKlassMap;
    public:
        bool check(ast::Specification *spec);

        ///getters
        const map<string, ast::Token *> &getNameTokenMap() const {
            return nameTokenMap;
        }

        const map<string, ast::Field *> &getNameFieldMap() const {
            return nameFieldMap;
        }

        const map<string, ast::Instruction *> &getNameInstrMap() const {
            return nameInstrMap;
        }

        const map<string, ast::Klass *> &getNameKlassMap() const {
            return nameKlassMap;
        }

        /// visitor methods
        bool visit(ast::ASTNode &node) override;

        bool visit(ast::TopDef &node) override;

        bool visit(ast::Name &node) override;

        bool visit(ast::Num &node) override;

        bool visit(ast::Token &node) override;

        bool visit(ast::Field &node) override;

        bool visit(ast::ConstraintBase &node) override;

        bool visit(ast::ConstraintBase::ConstraintRef &node) override;

        bool visit(ast::ConstraintBase::NameRef &node) override;

        bool visit(ast::ConstraintBase::ConstRef &node) override;

        bool visit(ast::ConjConstraint &node) override;

        bool visit(ast::SemiConstraint &node) override;

        bool visit(ast::EQConstraint &node) override;

        bool visit(ast::NEConstraint &node) override;

        bool visit(ast::NamedConstraint &node) override;

        bool visit(ast::Param &node) override;

        bool visit(ast::ParamList &node) override;

        bool visit(ast::UType &node) override;

        bool visit(ast::Instruction &node) override;

        bool visit(ast::SingleSemiConstraint &node) override;

        bool visit(ast::ClsConstraint &node) override;

        bool visit(ast::FldConstraint &node) override;

        bool visit(ast::Constructor &node) override;

        bool visit(ast::Klass &node) override;

        bool visit(ast::Specification &node) override;


    };

}


#endif //FRONTEND_TOKEN_CHECKER_HH
