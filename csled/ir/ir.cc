//
// Created by 徐翔哲 on 12/03/2020.
//


#include "ir.hh"
#include <string>
#include <iostream>
#include <map>
#include <sstream>
#include <algorithm>
#include <cassert>

//#define DEBUG


using namespace std;
namespace ir {
    map<string, IRType *> builtInTypes;
    namespace current {
        Definition *definition;
        vector<Param *> params;
        vector<BuiltInParam *> builtInParams;
        vector<UTypeParam *> utypeParams;
        ConjConstraint *conjConstraint;
        namespace binary {
            BitField *lhs;
            BuiltInParam *rhs1;
            Constant *rhs2;
            UTypeParam *rhs3;
            ConstraintRelation relation;

            void reset() {
                lhs = nullptr;
                rhs1 = nullptr;
                rhs2 = nullptr;
            }

            void tryBuild() {
                //at least one of the rhs is not null
                bool readyToBuild = lhs != nullptr && (rhs1 || rhs2);
                if (readyToBuild) {
                    bool onlyOneRHS = !(rhs1 && rhs2);
                    assert(onlyOneRHS);
                    if (rhs1) {
                        auto cons = new ParamConstraint(rhs1, lhs, relation);
                        conjConstraint->addPConstraint(cons);
                    } else if (rhs2) {
                        auto cons = new ConstConstraint(rhs2, lhs, relation);
                        conjConstraint->addCConstraint(cons);
                    } else {
                        //rhs3 can not be null here
                        assert(false);
                        auto cons = new UTypeConstraint(rhs3);
                        conjConstraint->addUTConstraint(cons);
                    }
                    reset();
                }
            }

        }

        void reset() {
            definition = nullptr;
            conjConstraint = nullptr;
            builtInTypes.clear();
            utypeParams.clear();
        }

        //if current definition doesn't have semi
        //or even doesn't have conj
        void createDefaultConstraintStructure() {
            conjConstraint = new ConjConstraint;
            definition->getConstraints().addConstraint(conjConstraint);
        }
    }


    bool ir::IRGenerator::visit(ast::ASTNode &node) {
        assert(false);
        return true;
    }

    bool ir::IRGenerator::visit(ast::TopDef &node) {
        assert(false);
        return true;
    }

    bool ir::IRGenerator::visit(ast::Name &node) {
        assert(false);
        return true;
    }

    bool ir::IRGenerator::visit(ast::Num &node) {
        assert(false);
        return true;
    }

    bool ir::IRGenerator::visit(ast::Token &node) {
        assert(false);
        return true;
    }

    bool ir::IRGenerator::visit(ast::Field &node) {
        assert(false);
        return true;
    }

    bool ir::IRGenerator::visit(ast::ConstraintBase &node) {
        assert(false);
        return true;
    }

    bool ir::IRGenerator::visit(ast::ConstraintBase::ConstraintRef &node) {
        assert(false);
        return true;
    }

    bool ir::IRGenerator::visit(ast::ConstraintBase::NameRef &node) {
        auto &name = node.getName();
        auto bfOpt = nameBFMap.find(name);
        if (bfOpt != nameBFMap.end()) {
            current::binary::lhs = bfOpt->second;
            return false;
        }

        cerr << node.getName() << endl;
        assert(false);
        return true;
    }

    bool ir::IRGenerator::visit(ast::ConstraintBase::ConstRef &node) {
        current::binary::rhs2 = new Constant(node.getNumber());
        current::binary::tryBuild();
        return false;
    }

    bool ir::IRGenerator::visit(ast::ConjConstraint &node) {
        if (current::conjConstraint == nullptr) {
            assert(false);
            current::createDefaultConstraintStructure();
        }
        return true;
    }

    bool ir::IRGenerator::visit(ast::SemiConstraint &node) {
        //enforce the order
        //if I am a part of another semi constraint, first delete the conjConstraint constructed by it
        //by doing this, we flatten a "tree" of semiConstrains to a vector of conjConstraints
        delete current::conjConstraint;

        current::conjConstraint = new ConjConstraint;
        node.getLhs().accept(*this);
        auto &semi = current::definition->getConstraints();
        //if lhs is not another semi
        if (current::conjConstraint != nullptr) {
            semi.addConstraint(current::conjConstraint);
        }

        current::conjConstraint = new ConjConstraint;
        node.getRhs().accept(*this);
        //if rhs is not another semi
        if (current::conjConstraint != nullptr) {
            semi.addConstraint(current::conjConstraint);
        }

        current::conjConstraint = nullptr;
        return false;
    }

    bool ir::IRGenerator::visit(ast::EQConstraint &node) {
        if (current::conjConstraint == nullptr) {
            assert(false);
            current::createDefaultConstraintStructure();
        }

        current::binary::reset();
        current::binary::relation = ConstraintRelation::EQ;
        //must be a nameref
        node.getLhs().accept(*this);
        //must be a const
        node.getRhs().accept(*this);
        return false;
    }

    bool ir::IRGenerator::visit(ast::NEConstraint &node) {
        if (current::conjConstraint == nullptr) {
            assert(false);
            current::createDefaultConstraintStructure();
        }

        current::binary::reset();
        current::binary::relation = ConstraintRelation::NE;
        //must be a nameref
        node.getLhs().accept(*this);
        //must be a const
        node.getRhs().accept(*this);
        return false;
    }

    bool ir::IRGenerator::visit(ast::NamedConstraint &node) {
        assert(false);
//        if (current::conjConstraint == nullptr) {
//            current::createDefaultConstraintStructure();
//        }
//        //this is a uType constraint in IR
//        auto &name = node.getName();
//        auto param = current::utypeParams.find(name);
//        assert(param != current::utypeParams.end());
//        current::conjConstraint->addUTConstraint(new UTypeConstraint(param->second));
        return false;
    }

    bool IRGenerator::visit(ast::ClsConstraint &node) {
        auto param = (UTypeParam *) current::params[node.getIndex() - 1];
        current::conjConstraint->addUTConstraint(new UTypeConstraint(param));
        return false;
    }

    bool IRGenerator::visit(ast::FldConstraint &node) {
        auto param = (BuiltInParam *) current::params[node.getIndex() - 1];
        current::conjConstraint->addPConstraint(new ParamConstraint(param, param->getRelatedField(), EQ));
        return false;
    }

    bool ir::IRGenerator::visit(ast::Param &node) {
        assert(false);
        return true;
    }

    bool ir::IRGenerator::visit(ast::ParamList &node) {
        assert(false);
        return true;
    }

    bool ir::IRGenerator::visit(ast::UType &node) {
        assert(false);
        return true;
    }

    bool ir::IRGenerator::visit(ast::Instruction &node) {
        assert(false);
        return true;
    }

    bool ir::IRGenerator::visit(ast::Specification &node) {
        return true;
    }

    void ir::IRGenerator::generate() {
        buildNameBPMap();
        buildIRUType();
//        buildInstruction();
    }

    void ir::IRGenerator::buildInstruction() {
        assert(false);
    }

    void ir::IRGenerator::buildIRUType() {
        //1. build params
        //2. build constraints
        //3. update utype map
        //4. patch utype params(after all utypes are resolved
        for (const auto &nameUType : nameKlassMap) {
            //1
            current::reset();
//            auto params = nameUType.second->getParamList().getParams();
            auto uType = new UType(nameUType.first);


            for (auto cons: nameUType.second->getConstructors()) {
                current::definition = new Definition;
                cons->accept(*this);
                current::definition->setName(cons->getConstructorName());
                uType->addDefinition(current::definition);
            }
            irNameUTypeMap.insert({nameUType.first, uType});
        }//end of per UType

        //4
        for (auto &nameUType:irNameUTypeMap) {
            auto &uType = nameUType.second;
            for (auto &def :uType->getDefinitions()) {
                for (auto &uTypeParam:def->getUTypeParams()) {
                    if (uTypeParam->getUType() == nullptr) {
                        auto &typeName = uTypeParam->getParamName();
                        auto uTypeOpt = irNameUTypeMap.find(typeName);
                        assert(uTypeOpt != irNameUTypeMap.end());
                        uTypeParam->setUType(uTypeOpt->second);
                    }
                }
            }
        }
#ifdef DEBUG
        cout << "DEBUG in UType Builder!" << endl;
        for (auto &nameUType:irNameUTypeMap) {
            cout << "typename: " << nameUType.first << endl;
            cout << "definitions: " << endl;
            for (auto &def :nameUType.second->getDefinitions()) {
                cout << "params: ";
                cout << "UType params: ";
                for (auto &param: def->getUTypeParams()) {
                    cout << param->getParamName() << ":"
                         << param->getUType()->getTypeName() << ", ";
                }
                cout << endl << "BuiltInParams: ";
                for (auto &param: def->getBuiltInParams()) {
                    cout << param->getParamName() << ": ub"
                         << param->getBuiltInType()->getWidth() << ", ";
                }
                cout << endl << "Constrains: " << endl;
                int i = 0;
                for (auto &semi: def->getConstraints().getConstraints()) {
                    cout << "SEMI " << i++ << ":" << endl;
                    cout << "\tConsts:" << endl;
                    for (auto &consts:semi->getCConstraints()) {
                        cout << "\t"
                             << consts->getToConstrain()->getName()
                             << toString(consts->getRelation())
                             << consts->getValue()->getValue()
                             << endl;
                    }
                    cout << "\tNames:" << endl;
                    for (auto &name:semi->getUtConstraints()) {
                        cout << "\t"
                             << name->getParam()->getParamName()
                             << ":" << name->getParam()->getUType()->getTypeName()
                             << endl;
                    }
                    cout << "\tBuiltIns:" << endl;
                    for (auto &builtIn: semi->getPConstraints()) {
                        cout << "\t"
                             << builtIn->getToConstrain()->getName()
                             << toString(builtIn->getRelation())
                             << builtIn->getParam()->getParamName()
                             << ": ub" << builtIn->getParam()->getBuiltInType()->getWidth()
                             << endl;
                    }
                }
            }
        }
#endif
    }

    void ir::IRGenerator::addCurrentParamForInstr(ast::Param *const &param) {
        assert(false);
    }

    void ir::IRGenerator::addCurrentParamForUType(ast::Param *const &param) {
        assert(false);
    }

    void IRGenerator::addBuiltInParam(ast::Param *const &param, const string &typeName) const {
        assert(false);
    }

    void ir::IRGenerator::buildNameBPMap() {
        //token to bf
        for (const auto &pair:nameTokenMap) {
            auto begin = pair.second->getTokenWidth() - 1;
            auto end = 0;
            auto bp = new BitField(pair.first, pair.second, begin, end);
            nameBFMap.insert({pair.first, bp});
        }
        //field to bf
        for (const auto &pair:nameFieldMap) {
            ast::Field *field = pair.second;
            auto tokenOpt = nameTokenMap.find(field->getTokenName());
            if (tokenOpt != nameTokenMap.end()) {
                //use copy constructor because the ownership of
                //original ast token should not be transferred to IR
                auto token = tokenOpt->second;
                auto myToken = new ast::Token(*token);
                auto bf = new BitField(pair.first, myToken, field->getBfBegin(), field->getBfEnd());
                nameBFMap.insert({pair.first, bf});
            } else {
                cerr << "Unable to find token for field " << field->getFieldName() << endl;
            }
        }
#ifdef DEBUG
        cout << "DEBUG in buildNameBPMap" << endl;
        for (const auto &pair:nameBFMap) {
            BitField *field = pair.second;
            cout << pair.first << " name: " << field->getName()
                 << ", tokenName: " << field->getToken()->getTokenName()
                 << ", begin: " << field->getBegin()
                 << ", end: " << field->getEnd() << endl;
        }
#endif

    }

    const map<string, BitField *> &IRGenerator::getNameBfMap() const {
        return nameBFMap;
    }

    const map<string, UType *> &IRGenerator::getIrNameUTypeMap() const {
        return irNameUTypeMap;
    }

    const map<string, Instruction *> &IRGenerator::getIrNameInstrMap() const {
        return irNameInstrMap;
    }

    bool IRGenerator::visit(ast::SingleSemiConstraint &node) {
        //COPY FROM SEMI CONSTRAINT
        delete current::conjConstraint;

        current::conjConstraint = new ConjConstraint;
        node.getLhs().accept(*this);
        auto &semi = current::definition->getConstraints();
        //if lhs is not another semi
        if (current::conjConstraint != nullptr) {
            semi.addConstraint(current::conjConstraint);
        }
        current::conjConstraint = nullptr;
        return false;
    }


    bool IRGenerator::visit(ast::Constructor &node) {
        current::params.clear();
        auto args = node.getAids();
        //1. prepare the parameters
        for (int i = 0; i < args.size(); i++) {
            const auto &name = args[i];
            auto optBF = this->nameBFMap.find(name);
            if (optBF != this->nameBFMap.end()) {
                auto width = optBF->second->getWidth();
                auto builtin = new BuiltInParam(new UnsignedBits(width),
                                                "uvar" + to_string(width) + "_" + to_string(i), optBF->second);
                current::params.push_back(builtin);
                current::definition->addBuiltInParam(builtin);
            } else {
                auto utParam = new UTypeParam(nullptr, *new string(name));
                current::params.push_back(utParam);
                current::definition->addUTypeParams(utParam);
            }
        }
        //2. build constraints
        node.getPattern().accept(*this);

        return false;
    }

    bool IRGenerator::visit(ast::Klass &node) {
        assert(false);
        return false;
    }

    bool UTypeConstraint::isFullyQualified() {
        auto defs = param->getUType()->getDefinitions();
        for (auto def: defs) {

        }
        return true;
    }

    auto pcToBp = [](const ParamConstraint *p) -> const BitField * {
        return p->getToConstrain();
    };
    auto ccToBp = [](const ConstConstraint *c) -> BitField * {
        return c->getToConstrain();
    };

    bool isFullyQualified(const ast::Token *token, vector<const BitField *> &bfs) {
        auto width = token->getTokenWidth();
        auto bits = vector<bool>(width, false);
        for (auto bf:bfs) {
            for (int i = bf->getBegin(); i >= bf->getEnd(); i--) {
                bits[width - 1 - i] = true;
            }
        }
        //every bit is true
        return find(bits.begin(), bits.end(), false) == bits.end();
    }

    bool ConjConstraint::isFullyQualified() {
        const ast::Token *optionToken = nullptr;
        vector<const BitField *> explicitBitFields;
        extractTokenBf(optionToken, explicitBitFields);
        if (!utConstraints.empty()) {
            assert(utConstraints.size() == 1);
            return isUTConstraintContextualFQ(optionToken, explicitBitFields, utConstraints[0]);
        }
        if (optionToken == nullptr) {
            return false;
        }
        return ir::isFullyQualified(optionToken, explicitBitFields);
    }

    bool ConjConstraint::isUTConstraintContextualFQ(const ast::Token *optionToken,
                                                    const vector<const BitField *> &explicitBitFields,
                                                    UTypeConstraint *utCons) {
        if (utCons->isFullyQualified()) {
            return true;
        } else {
            if (optionToken == nullptr) {
                return false;
            }
            auto ut = utCons->getParam()->getUType();
            bool result = true;
            for (auto def:ut->getDefinitions()) {
                if (!def->getConstraints().getConstraints().empty()) {
                    vector<const BitField *> bitFields(explicitBitFields);
                    auto firstSemi = def->getConstraints().getConstraints()[0];
                    transform(firstSemi->pConstraints.begin(), firstSemi->pConstraints.end(),
                              back_inserter(bitFields), pcToBp);
                    transform(firstSemi->cConstraints.begin(), firstSemi->cConstraints.end(),
                              back_inserter(bitFields), ccToBp);
                    result &= ir::isFullyQualified(optionToken, bitFields);
                }
            }
            return result;
        }
    }

    void ConjConstraint::extractTokenBf(const ast::Token *&optionToken, vector<const BitField *> &explicitBitFields) {
        transform(pConstraints.begin(), pConstraints.end(),
                  back_inserter(explicitBitFields), pcToBp);
        transform(cConstraints.begin(), cConstraints.end(),
                  back_inserter(explicitBitFields), ccToBp);
        if (!pConstraints.empty()) {
            optionToken = pConstraints[0]->getToConstrain()->getToken();
        } else if (!cConstraints.empty()) {
            optionToken = cConstraints[0]->getToConstrain()->getToken();
        }
    }

    string toString(const ConstraintRelation &relation) {
        switch (relation) {
            case EQ:
                return "==";

            case NE:
                return "!=";
        }
    }

    bool Definition::isFullyQualified() {
        return constraints.isFullyQualified();
    }

    bool SemiConstraint::isFullyQualified() {
        for (auto cons:constraints) {
            if (!cons->isFullyQualified()) {
                return false;
            }
        }
        return true;
    }
}