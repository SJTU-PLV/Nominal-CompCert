//
// Created by 徐翔哲 on 12/27/2020.
//

#include "encoder.hh"
#include "coqgen.hh"
#include <string>
#include <iostream>
#include <vector>
#include "../ir/ir.hh"
#include <sstream>
#include "encoder.hh"
#include "util.hh"
#include <cassert>
#include <algorithm>



namespace coq {


    namespace encoder {


        //convention: result stores in result<semiCnt>
        vector<Statement *> *_conjunctionToStatements(ir::ConjConstraint *conj, int semiCnt) {
            auto ret = new vector<Statement *>;
            string prefix = "bits";
            int localCnt = 0;
            bool lastIsList = false;
            // FIXME: here we assume all the prefix token has one byte width
            // that means only the first semi could use the input byte.
            // All the following non-FQ should use ["00"] as the default

            // UPDATE 2022.10.1: try to use bits as the placeholder with arbitrary length instead of just one byte
            // which supports that some fields cross two bytes. 
            bool hasExtraOutPut = !conj->isFullyQualified();

            // get the token length where the constant and parameter constraints reside in
            int tokenLength = -1;
            if (!conj->getCConstraints().empty()) {
                tokenLength = conj->getCConstraints()[0]->getLength();
            } else if (!conj->getPConstraints().empty()) {
                tokenLength = conj->getPConstraints()[0]->getLength();
            }
            if (tokenLength == -1) {
                assert(false);
                return ret;
            }

            //prepare the start byte
            if (hasExtraOutPut && semiCnt == 0) {
                auto *start = new LetStatement;
                start->bind = prefix + to_string(semiCnt) + to_string(localCnt++);
                start->expr = "inBits";
                ret->push_back(start);
            } else {
                auto *start = new LetStatement;
                start->bind = prefix + to_string(semiCnt) + to_string(localCnt++);
                // start->expr = "HB[\"00\"]";
                start->expr = "(repeat false " + to_string(tokenLength) + ")";
                ret->push_back(start);
            }
            //write const constraints
            for (auto cons:conj->getCConstraints()) {
                if(cons->getRelation()!=ir::EQ){
                    continue;
                }
                auto previousBits = prefix + to_string(semiCnt) + to_string(localCnt - 1);
                if (!cons->getToConstrain()->isSubField()) {
                    //if this is a token
                    //clear all the previous constraints for this semi
                    for_each(ret->begin(), ret->end(), [](Statement *s) -> void { delete s; });
                    ret->clear();
                    // use the constant bits to represent this token
                    auto *write = new LetStatement;
                    write->bind = prefix + to_string(semiCnt) + to_string(localCnt++);
                    write->expr = util::_valueToBits(cons->getValue()->getValue(), cons->getToConstrain()->getWidth());
                    ret->push_back(write);
                } else {
                    //if this is not a token
                    auto *write = new LetStatement;
                    write->bind = prefix + to_string(semiCnt) + to_string(localCnt++);
                    auto &bfName = cons->getToConstrain()->getName();
                    auto writeBF = "write_" + bfName;
                    write->expr = writeBF.append(" ")
                            .append(previousBits)
                            .append(" ")
                            .append(util::_valueToBits(cons->getValue()->getValue(),
                                                       cons->getToConstrain()->getWidth()));
                    ret->push_back(write);
                }

            }
            //write param cons
            for (auto pCons:conj->getPConstraints()) {
                auto previousBits = prefix + to_string(semiCnt) + to_string(localCnt - 1);
                if (!pCons->getToConstrain()->isSubField()) {
                    //if this is a token
                    //clear all the previous constraints for this semi
                    for_each(ret->begin(), ret->end(), [](Statement *s) -> void { delete s; });
                    ret->clear();
                    int width = pCons->getToConstrain()->getWidth();

                    auto *write = new LetStatement;
                    write->bind = prefix + to_string(semiCnt) + to_string(localCnt++);
                    write->expr = util::proj1(pCons->getParam()->getParamName());
                    ret->push_back(write);
                    
                } else {
                    //if this is not a token
                    auto width = pCons->getParam()->getBuiltInType()->getWidth();
                    auto *write = new LetStatement;
                    write->bind = prefix + to_string(semiCnt) + to_string(localCnt++);
                    auto &bfName = pCons->getToConstrain()->getName();
                    auto writeBF = "write_" + bfName;
                    write->expr = writeBF.append(" ")
                            .append(previousBits)
                            .append(" ")
                            .append(util::proj1(pCons->getParam()->getParamName()));
                    ret->push_back(write);
                }
            }
            //write utype cons
            for (auto uCons:conj->getUtConstraints()) {
                auto previousBits = prefix + to_string(semiCnt) + to_string(localCnt - 1);
                auto *write = new DoStatement;
                write->bind = prefix + to_string(semiCnt) + to_string(localCnt++);
                auto uType = uCons->getParam()->getUType();
                auto &uTName = uType->getTypeName();
                auto encoderName = "encode_" + uTName;
                if (uType->isFullyQualified()) {
                    write->expr = encoderName.append(" ")
                            .append(uCons->getParam()->getParamName());
                } else {
                    write->expr = encoderName.append(" ")
                            .append(uCons->getParam()->getParamName())
                            .append(" ")
                            .append(previousBits);
                }
                ret->push_back(write);
            }
            auto retStmt = new LetStatement;
            auto previousBits = prefix + to_string(semiCnt) + to_string(localCnt - 1);
            retStmt->bind = "result" + to_string(semiCnt);
            retStmt->expr = previousBits;

            ret->push_back(retStmt);
            return ret;
        }

        //find the parameter used to assign a bit field
        string _searchParameterByBitField(const string &fieldName, ir::Definition *def) {
            for (auto conj:def->getConstraints().getConstraints()) {
                for (auto pcons:conj->getPConstraints()) {
                    if (fieldName == pcons->getToConstrain()->getName()) {
                        return pcons->getParam()->getParamName();
                    }
                }
            }
            assert(false);
        }

        //convention: empty or if ... else <empty>
        vector<Statement *> *_checkNeqConstraints(ir::Definition *def) {
            auto ret = new vector<Statement *>;
            auto conjs = def->getConstraints();
            for (auto conj:conjs.getConstraints()) {
                for (auto constConstraint: conj->getCConstraints()) {
                    if (constConstraint->getRelation() == ir::NE) {
                        auto &fieldName = constConstraint->getToConstrain()->getName();
                        auto paramName = _searchParameterByBitField(fieldName, def);
                        auto guard = new IfThenElse;
                        guard->condition = "builtin_eq_dec " + util::proj1(paramName)
                                           + util::_valueToBits(constConstraint->getValue()->getValue(),
                                                                constConstraint->getToConstrain()->getWidth());
                        guard->thenStmts.push_back(new ErrorStmt("Constraint Failed"));
                        ret->push_back(guard);
                    }
                }
            }
            return ret;
        }

        vector<Statement *> *_fromConstraintToStatements(ir::Definition *def) {
            auto ret = new vector<Statement *>;
            auto conjs = def->getConstraints().getConstraints();
            int semiCnt = 0;
            //generate checks
            auto checks = _checkNeqConstraints(def);
            ret->insert(ret->end(), checks->begin(), checks->end());
            delete checks;
            //generate encoding stmts
            vector<vector<Statement *> *> conjResults;
            for (auto conj:conjs) {
                auto stmts = _conjunctionToStatements(conj, semiCnt);
                semiCnt++;
                conjResults.push_back(stmts);
            }
            for (auto results:conjResults) {
                ret->insert(ret->end(), results->begin(), results->end());
                delete results;
            }
            stringstream returnStmt;
            returnStmt << "OK (";
            bool first = true;
            for (int i = 0; i < semiCnt; i++) {
                if (!first) {
                    returnStmt << " ++ ";
                } else {
                    first = false;
                }
                returnStmt << "result" + to_string(i);
            }
            returnStmt << ")";
            ret->push_back(new Statement(returnStmt.str()));
            return ret;
        }

        bool _isFullyQualified(vector<pair<string, ir::Definition *>> &variants) {
            for (auto &nameDef:variants) {
                if (!nameDef.second->isFullyQualified()) {
                    return false;
                }
            }
            return true;
        }

        static const char *const ELEMENT = "element";

        string getEncoder(const string &varName, vector<pair<string, ir::Definition *>> &variants) {
            Definition funcDef;
            MatchStatement matchStatement;
            //initialize
            funcDef.name = "encode_" + varName;
            string paramName = ELEMENT;
            funcDef.params.push_back(new Parameter(paramName, ""));
            auto hasAdditionalParameter = !_isFullyQualified(variants);
            if (hasAdditionalParameter) {
                funcDef.params.push_back(new Parameter("inBits", ""));
            }
            matchStatement.variable = paramName;
            for (auto &nameDef: variants) {
                //generate match arm
                auto arm = new MatchArm;
                //the arm head
                arm->constructor = nameDef.first;
                //the order is VERY important!!!!
                //UT first, then BuiltIn
                for (auto param:nameDef.second->getUTypeParams()) {
                    arm->params.push_back(param->getParamName());
                }
                for (auto param:nameDef.second->getBuiltInParams()) {
                    arm->params.push_back(param->getParamName());
                }
                //the arm body
                auto stmts = _fromConstraintToStatements(nameDef.second);
                arm->stmts.insert(arm->stmts.end(), stmts->begin(), stmts->end());
                delete stmts;
                matchStatement.branches.push_back(arm);
            }
            funcDef.body.push_back(&matchStatement);
            auto ret = funcDef.toString();
            //FIXME: plenty of memory leak
            return ret;
        }
    }

    string Encoder::generateEncoder() {

        sout << encoder::getEncoder(variantsName, variants);
        auto ret = sout.str();
        sout.clear();
        return ret;
    }
}