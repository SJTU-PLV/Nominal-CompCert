//
// Created by 徐翔哲 on 12/03/2020.
//

#ifndef FRONTEND_IR_HH
#define FRONTEND_IR_HH

#include <string>
#include <utility>
#include <vector>
#include <iostream>
#include <sstream>
#include <map>
#include "types.hh"
#include "../parser/visitor.hh"

using namespace std;

namespace ir {
    enum ConstraintRelation {
        EQ, NE
    };

    string toString(const ConstraintRelation &relation);

    //both field and token become BitField in IR
    class BitField {
    private:
        string name;
        ast::Token *token;
        int begin, end;
    public:
        bool isSubField() const {
            return !(begin == token->getTokenWidth() - 1 && end == 0);
        }

    public:
        BitField(const string &name, ast::Token *token, int begin, int end)
                : name(name), token(token), begin(begin), end(end) {}

        const string &getName() const {
            return name;
        }

        const ast::Token *getToken() const {
            return token;
        }

        int getBegin() const {
            return begin;
        }

        int getEnd() const {
            return end;
        }

        int getWidth() const {
            return begin - end + 1;
        }
    };

    class Param{

    };

    class BuiltInParam:public Param {
    private:
        const UnsignedBits *builtInType;
        const string paramName;
        const BitField *relatedField;
    public:
//        BuiltInParam(const UnsignedBits *builtInType, string paramName)
//                : builtInType(builtInType), paramName(std::move(paramName)) {}

        BuiltInParam(const UnsignedBits *builtInType, const string &paramName, const BitField *relatedField)
                : builtInType(builtInType), paramName(paramName), relatedField(relatedField) {}

        const UnsignedBits *getBuiltInType() const {
            return builtInType;
        }

        const string &getParamName() const {
            return paramName;
        }

        const BitField *getRelatedField() const {
            return relatedField;
        }

    };

    class UTypeParam: public Param {
    private:
        UType *uType;
        string paramName;
    public:
        UTypeParam(UType *uType, string paramName) : uType(uType), paramName(std::move(paramName)) {}

        UType *getUType() const {
            return uType;
        }

        void setUType(UType *uType) {
            this->uType = uType;
        }

        const string &getParamName() const {
            return paramName;
        }

    };

    class ConstConstraint {
    private:
        Constant *value;
        BitField *toConstrain;
        ConstraintRelation relation;
    public:
        ConstConstraint(Constant *value, BitField *toConstrain, ConstraintRelation r)
                : value(value), toConstrain(toConstrain), relation(r) {}

        Constant *getValue() const {
            return value;
        }

        BitField *getToConstrain() const {
            return toConstrain;
        }

        ConstraintRelation getRelation() const {
            return relation;
        }

        bool isFixLength() const {
            return true;
        }

        int getLength() const {
            return toConstrain->getToken()->getTokenWidth();
        }

    };


    class ParamConstraint {
    private:
        BuiltInParam *param;
        const BitField *toConstrain;
        ConstraintRelation relation;
    public:
        ParamConstraint(BuiltInParam *param, const BitField *toConstrain, ConstraintRelation relation)
                : param(param), toConstrain(toConstrain), relation(relation) {}

        BuiltInParam *getParam() const {
            return param;
        }

        const BitField *getToConstrain() const {
            return toConstrain;
        }

        ConstraintRelation getRelation() const {
            return relation;
        }

        bool isFixLength() const {
            return true;
        }

        int getLength() const {
            return toConstrain->getToken()->getTokenWidth();
        }
    };

    class UTypeConstraint {
    private:
        UTypeParam *param;
    public:
        UTypeConstraint(UTypeParam *param) : param(param) {}

        UTypeParam *getParam() const {
            return param;
        }

        bool isFixLength() const {
            return param->getUType()->isFixLength();
        }

        int getLength() const {
            return param->getUType()->getLength();
        }

        bool isFullyQualified();
    };

    class ConjConstraint {
        vector<UTypeConstraint *> utConstraints;
        //we assume that all the const constraints &
        //param constraints are on the same token
        vector<ParamConstraint *> pConstraints;
        vector<ConstConstraint *> cConstraints;
    public:
        ConjConstraint() = default;

        void addUTConstraint(UTypeConstraint *ut) {
            utConstraints.push_back(ut);
        }

        void addPConstraint(ParamConstraint *p) {
            pConstraints.push_back(p);
        }

        void addCConstraint(ConstConstraint *c) {
            cConstraints.push_back(c);
        }

        const vector<UTypeConstraint *> &getUtConstraints() const {
            return utConstraints;
        }

        const vector<ParamConstraint *> &getPConstraints() const {
            return pConstraints;
        }

        const vector<ConstConstraint *> &getCConstraints() const {
            return cConstraints;
        }

        bool isFixLength() {
            if (utConstraints.empty()) {
                return true;
            } else {
                bool isFix = true;
                for (auto &cons: utConstraints) {
                    isFix &= cons->isFixLength();
                }
                return isFix;
            }
        }

        bool hasFixLengthPrefix() {
            return !(this->getPConstraints().empty() && this->getCConstraints().empty());
        }

        bool isFullyQualified();

        string toString() {
            stringstream sout;
            for (auto &cons: utConstraints) {
                sout << cons->getParam()->getParamName() << "&";
            }
            for (auto &cons: cConstraints) {
                sout << cons->getToConstrain()->getName()
                     << ((cons->getRelation() == EQ) ? "==" : "!=")
                     << cons->getValue()->getValue()
                     << "&";
            }
            for (auto &cons: pConstraints) {
                sout << cons->getToConstrain()->getName()
                     << ((cons->getRelation() == EQ) ? "==" : "!=")
                     << cons->getParam()->getParamName()
                     << "&";
            }
            return sout.str();
        }

    private:
        void extractTokenBf(const ast::Token *&optionToken, vector<const BitField *> &explicitBitFields);

        bool isUTConstraintContextualFQ(const ast::Token *optionToken, const vector<const BitField *> &explicitBitFields,
                                        UTypeConstraint *utCons);
    };

    class SemiConstraint {
        vector<ConjConstraint *> constraints;
    public:
        SemiConstraint() = default;

        void addConstraint(ConjConstraint *c) {
            constraints.push_back(c);
        }

        const vector<ConjConstraint *> &getConstraints() const {
            return constraints;
        }

        string toString() {
            stringstream sout;
            for (int i = 0; i < constraints.size(); i++) {
                sout << "SEMI" << i << ": ";
                sout << constraints[i]->toString() << endl;
            }
            return sout.str();
        }

        bool isFullyQualified();
    };

    class Definition {
        string name;
        SemiConstraint constraints;
        vector<BuiltInParam *> builtInParams;
        vector<UTypeParam *> uTypeParams;
    public:
        Definition() = default;


        void addBuiltInParam(BuiltInParam *param) {
            builtInParams.push_back(param);
        }

        void addUTypeParams(UTypeParam *param) {
            uTypeParams.push_back(param);
        }

        const vector<BuiltInParam *> &getBuiltInParams() const {
            return builtInParams;
        }

        const vector<UTypeParam *> &getUTypeParams() const {
            return uTypeParams;
        }

        SemiConstraint &getConstraints() {
            return constraints;
        }

        const SemiConstraint &getConstraints()const {
            return constraints;
        }

        string toString() {
            return constraints.toString();
        }

        bool isFullyQualified();

        const string &getName() const {
            return name;
        }

        void setName(const string &name) {
            Definition::name = name;
        }
    };

    class IRGenerator : public ast::ASTVisitor {
        const map<string, ast::Token *> &nameTokenMap;
        const map<string, ast::Field *> &nameFieldMap;
        const map<string, ast::Klass *> &nameKlassMap;
        const ast::Specification *spec;
        ///our representation
        map<string, BitField *> nameBFMap;
        map<string, UType *> irNameUTypeMap;
        map<string, Instruction *> irNameInstrMap;
    private:
        void buildNameBPMap();

        void buildIRUType();

        void buildInstruction();

        void addCurrentParamForUType(ast::Param *const &param);

        void addCurrentParamForInstr(ast::Param *const &param);

    public:
        IRGenerator(const map<string, ast::Token *> &nameTokenMap, const map<string, ast::Field *> &nameFieldMap,
                    const map<string, ast::Klass *> &nameKlassMap,
                    const ast::Specification *spec)
                : nameTokenMap(nameTokenMap), nameFieldMap(nameFieldMap),
                  nameKlassMap(nameKlassMap), spec(spec) {}

        void generate();

        const map<string, BitField *> &getNameBfMap() const;

        const map<string, UType *> &getIrNameUTypeMap() const;

        const map<string, Instruction *> &getIrNameInstrMap() const;

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

        bool visit(ast::Specification &node) override;

        bool visit(ast::SingleSemiConstraint &node) override;

        bool visit(ast::ClsConstraint &node) override;

        bool visit(ast::FldConstraint &node) override;

        bool visit(ast::Constructor &node) override;

        bool visit(ast::Klass &node) override;

        void addBuiltInParam(ast::Param *const &param, const string &typeName) const;
    };


}


#endif //FRONTEND_IR_HH
