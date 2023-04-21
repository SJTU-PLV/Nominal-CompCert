//
// Created by 徐翔哲 on 01/10/2021.
//

#include "spec_printer.hh"
#include <string>
#include <iostream>
#include <vector>
#include "../ir/ir.hh"
#include "coqgen.hh"
#include <sstream>
#include <algorithm>
#include "util.hh"
#include <cassert>
#include <utility>

static const char *const SPEC_SUFFIX = "_spec";
static const char *const INPUT = "lst";
namespace coq {
    string inductiveSpecHead(const string &funcName, const vector<string> &types) {
        stringstream ret;
        ret << "Inductive ";
        ret << funcName;
        ret << ": ";
        for (const auto &t : types) {
            ret << t << " -> ";
        }
        ret << "Prop :=" << endl;
        return ret.str();
    }

    static const char *const CONJUNC = " /\\ ";

#pragma clang diagnostic push
#pragma ide diagnostic ignored "performance-inefficient-string-concatenation"

    static string _getSpecificationForConstrains(const ir::SemiConstraint &cons,
                                                 const map<string, vector<ir::BitField *> *> &tokenBFs,
                                                 bool prefix = false) {
        vector<string> components;
        vector<string> constraints;
        int conjCnt = 0;
        for (auto &conj:cons.getConstraints()) {
            const ast::Token *currentToken = nullptr;
            vector<string> currentComponents;
            bool shouldBreak = true;
            //get current token
            if (!conj->getCConstraints().empty()) {
                auto firstConstraint = conj->getCConstraints()[0];
                currentToken = firstConstraint->getToConstrain()->getToken();
                shouldBreak = firstConstraint->getToConstrain()->isSubField();
            } else if (!conj->getPConstraints().empty()) {
                auto firstConstraint = conj->getPConstraints()[0];
                currentToken = firstConstraint->getToConstrain()->getToken();
                shouldBreak = firstConstraint->getToConstrain()->isSubField();
            }
            //get current components and length constraints
            if (currentToken != nullptr) {
                auto nameBFs = tokenBFs.find(currentToken->getTokenName());

                if (nameBFs != tokenBFs.end() && shouldBreak) {
                    for (auto &bf:*nameBFs->second) {
                        auto varName = bf->getName() + to_string(conjCnt);
                        currentComponents.push_back(varName);
                        auto varCons = "length " + varName + " = " + to_string(bf->getWidth());
                        constraints.push_back(varCons);
                    }
                } else {
                    //for token which has no subfields
                    // or for token referred as a whole
                    auto varName = currentToken->getTokenName() + to_string(conjCnt);
                    currentComponents.push_back(varName);
                    auto varCons = "length " + varName + " = " + to_string(currentToken->getTokenWidth());
                    constraints.push_back(varCons);
                }
            }

            for (auto &ccons:conj->getCConstraints()) {
                auto bfName = ccons->getToConstrain()->getName();
                auto varName = bfName + to_string(conjCnt);
                auto consValue = util::_valueToBits(ccons->getValue()->getValue(),
                                                    ccons->getToConstrain()->getWidth());
                if (ccons->getRelation() == ir::EQ) {
                    constraints.push_back(varName + " = " + consValue);
                } else {
                    constraints.push_back(varName + " <> " + consValue);
                }
            }

            for (auto &pcons:conj->getPConstraints()) {
                auto bfName = pcons->getToConstrain()->getName();
                auto varName = bfName + to_string(conjCnt);
                auto param = pcons->getParam()->getParamName();
                if (pcons->getRelation() == ir::EQ) {
                    constraints.push_back(varName + " = " + util::proj1(param));
                } else {
                    //parameter constraints should not contain neq
                    assert(false);
                }
            }

            if (!conj->getUtConstraints().empty()) {
                auto ucons = conj->getUtConstraints()[0];
                auto consName = ucons->getParam()->getParamName();
                auto varName = consName + to_string(conjCnt);
                currentComponents.push_back(varName);
                stringstream currentComponentsStr;
                currentComponentsStr << "(";
                bool first = true;
                for (auto &comp: currentComponents) {
                    if (first) {
                        first = false;
                    } else {
                        currentComponentsStr << " ++ ";
                    }
                    currentComponentsStr << comp;
                }
                currentComponentsStr << ") " << ucons->getParam()->getParamName();
                auto utypeName = ucons->getParam()->getUType()->getTypeName();
                auto constraint = utypeName + SPEC_SUFFIX + " " + currentComponentsStr.str();
                constraints.push_back(constraint);
            }
            components.insert(components.end(), currentComponents.begin(), currentComponents.end());

            conjCnt++;
        }
        if (prefix) {
            components.emplace_back("tail");
        }
        stringstream ret;
        ret << "exists";
        for (auto &comp: components) {
            ret << " " << comp;
        }
        ret << "," << endl;
        ret << "lst = ";
        bool first = true;
        for (auto &comp: components) {
            if (first) {
                first = false;
            } else {
                ret << " ++ ";
            }
            ret << comp;
        }
        ret << endl;
        for (auto &constraint:constraints) {
            ret << CONJUNC << constraint;
        }
        return ret.str();
    }

#pragma clang diagnostic pop

    static string getSpecificationForDefinition(const string &variantName,
                                                const string &name, const ir::Definition *definition,
                                                const map<string, vector<ir::BitField *> *> &tokenBFs) {
        auto funcName = name + SPEC_SUFFIX;
        stringstream params;
        stringstream ret;
        vector<string> types;
        types.emplace_back("list bool");
        params << INPUT;
        for (auto &utParam: definition->getUTypeParams()) {
            types.push_back(utParam->getUType()->getTypeName());
            params << " " << utParam->getParamName();
        }
        for (auto &builtInParam: definition->getBuiltInParams()) {
            auto builtInName = builtInParam->getBuiltInType()->toString();
            types.push_back(builtInName);
            params << " " << builtInParam->getParamName();
        }
        auto head = inductiveSpecHead(funcName, types);
        ret << head;
        ret << "|cons_" << name << ":" << endl;
        ret << "forall ";
        ret << params.str();
        ret << endl;
        ret << "(CONS: ";
        //spec body
        ret << _getSpecificationForConstrains(definition->getConstraints(),
                                              tokenBFs,
                                              variantName == "instruction");

        ret << ")," << endl;
        ret << funcName << " " << params.str() << ".";
        return ret.str();
    }


    static string getSpecDefinition(const string &variantsName,
                                    const vector<pair<string, ir::Definition *>> &variants) {
        Definition funDef;
        funDef.name = variantsName + SPEC_SUFFIX;
        Parameter input(INPUT, "");
        funDef.params.push_back(&input);
        Parameter varInput("element", "");
        funDef.params.push_back(&varInput);
        funDef.retValue = "Prop";

        auto stmt = new MatchStatement;
        funDef.body.push_back(stmt);
        stmt->variable = "element";
        for (const auto &nameDef:variants) {
            auto arm = new MatchArm;
            arm->constructor = nameDef.first;
            for (auto utypeParam:nameDef.second->getUTypeParams()) {
                arm->params.push_back(utypeParam->getParamName());
            }
            for (auto builtInParam: nameDef.second->getBuiltInParams()) {
                arm->params.push_back(builtInParam->getParamName());
            }
            stringstream stmtStream;
            stmtStream << nameDef.first << SPEC_SUFFIX << " ";
            stmtStream << INPUT;
            for (auto &param:arm->params) {
                stmtStream << " " << param;
            }
            arm->stmts.push_back(new Statement(stmtStream.str()));
            stmt->branches.push_back(arm);
        }
        return funDef.toString();
    }

    void coq::SpecPrinter::preprocess() {
        for (auto &nameBF:nameBFMap) {
            if (nameBF.second->isSubField()) {
                auto &tokenName = nameBF.second->getToken()->getTokenName();
                auto optionTokenNameBFs = tokenNameBFMap.find(tokenName);
                if (optionTokenNameBFs == tokenNameBFMap.end()) {
                    tokenNameBFMap.insert({tokenName,
                                           new vector<ir::BitField *>{nameBF.second}});
                } else {
                    optionTokenNameBFs->second->push_back(nameBF.second);
                }
            }
        }

        for (auto &tokenNameBFs:tokenNameBFMap) {
            sort(tokenNameBFs.second->begin(), tokenNameBFs.second->end(),
                 [](ir::BitField *bf1, ir::BitField *bf2) -> bool {
                     return (bf1->getBegin() > bf2->getBegin());
                 });
        }


//        for (const auto &tokenNameBFs:tokenNameBFMap) {
//            cout << tokenNameBFs.first << ": ";
//            for (auto bf:*tokenNameBFs.second) {
//                cout << bf->getName() << " ";
//            }
//            cout << endl;
//        }
    }

    string coq::SpecPrinter::generateSpecs() {
        preprocess();
        for (auto &nameDef: variants) {
            sout << getSpecificationForDefinition(variantsName, nameDef.first,
                                                  nameDef.second, tokenNameBFMap);
            sout << endl;
        }
        sout << getSpecDefinition(variantsName, variants);
        return sout.str();
    }
}