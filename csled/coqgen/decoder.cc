//
// Created by 徐翔哲 on 12/30/2020.
//

#include "decoder.hh"
#include "../ir/ir.hh"
#include "coqgen.hh"
#include <string>
#include <vector>
#include <algorithm>
#include <sstream>
#include <map>
#include <cassert>
#include <utility>

using namespace std;
namespace coq {
    static void _generateSkipN(DoStatement *stmt, const string &bindName,
                               const string &listName, const string &n) {
        stmt->bind = bindName;
        stmt->expr = "try_skip_n " + listName + " " + n;

    }

    static const char *const LENGTH_EVIDENCE_SUFFIX = "_len";

    vector<Statement *> *getDecoderBodyForSingleDefinition(const string &constructorName,
                                                           ir::Definition *definition) {
        string codePrefix = "code";
        string tokenPrefix = "token";
        string sizePrefix = "localLength";
        int codeCnt = 0;
        int tokenCnt = 0;
        int sizeCnt = 0;
        int lengthCnt = 0;
        //the cnt of length assert
        int assertionCnt = 0;
        auto ret = new vector<Statement *>;
        auto start = new LetStatement;
        start->bind = codePrefix + to_string(codeCnt++);
        start->expr = "bin";
        ret->push_back(start);
        for (auto conj:definition->getConstraints().getConstraints()) {
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

            if (conj->getPConstraints().empty() && conj->getUtConstraints().empty()) {
                // FIXME: we assume that the only constant constrain occupies the whole token
                // we can not solve this one
                // constr ecall [] (opcode = 0x73 & rd = 0x0 & funct3 = 0x0 & rs1 = 0x0 & immI = 0x0)

                //if this constraint only contains consts, we should skip it since
                //all the consts are checked in the bit pattern
                auto skip = new DoStatement;
                auto previous = codePrefix + to_string(codeCnt - 1);
                auto bindName = codePrefix + to_string(codeCnt++);
                _generateSkipN(skip, bindName, previous, to_string(tokenLength));
                //consume one token and calculate the length of bytes of this token
                lengthCnt += tokenLength;
                ret->push_back(skip);
                continue;
            }
            if (!conj->getPConstraints().empty()) {
                // FIXME: We assume subfields only appear in single byte tokens,
                // see `Instr.md` for more information
                // 2022.10.1: support writing cross bytes filed
                auto currentCode = codePrefix + to_string(codeCnt - 1);
                if (conj->getPConstraints()[0]->getToConstrain()->isSubField()) {
                    auto currentToken = tokenPrefix + to_string(tokenCnt++);
                    auto getToken = new DoStatement;
                    getToken->bind = currentToken;
                    getToken->expr = "try_first_n " + currentCode + " " + to_string(tokenLength);
                    ret->push_back(getToken);
                    //deal with pcons
                    for (auto pCons:conj->getPConstraints()) {
                        auto bf = pCons->getToConstrain();
                        auto &bfName = bf->getName();
                        auto readerName = "read_" + bfName;
                        auto *param = pCons->getParam();
                        auto &paramName = param->getParamName();
                        auto readField = new LetStatement;
                        readField->bind = paramName;
                        readField->expr = readerName.append(" ")
                                .append(currentToken);
                        ret->push_back(readField);
                        //about length
                        auto assertLen = new Statement;
                        auto width = param->getBuiltInType()->getWidth();
                        assertLen->anything = "if assertLength "
                                              + paramName + " " + to_string(width) + " then";
                        assertionCnt++;
                        ret->push_back(assertLen);
                    }
                } else {
                    assert(conj->getPConstraints().size() == 1);
                    auto cons = conj->getPConstraints()[0];

                    auto currentToken = tokenPrefix + to_string(tokenCnt++);
                    auto getToken = new DoStatement;
                    getToken->bind = currentToken;
                    getToken->expr = "try_first_n " + currentCode + " " + to_string(tokenLength);
                    ret->push_back(getToken);

                    auto toParam = new LetStatement;
                    auto param = cons->getParam();
                    auto &paramName = param->getParamName();
                    toParam->bind = paramName;
                    toParam->expr = currentToken;
                    ret->push_back(toParam);

                    //about length
                    auto assertLen = new Statement;
                    assertLen->anything = "if assertLength "
                                          + paramName + " " + to_string(tokenLength) + " then";
                    assertionCnt++;
                    ret->push_back(assertLen);
                }
            }
            if (!conj->getUtConstraints().empty()) {
                assert(conj->getUtConstraints().size() == 1);
                auto uCons = conj->getUtConstraints()[0];
                auto paramName = uCons->getParam()->getParamName();
                auto sizeRetName = sizePrefix + to_string(sizeCnt++);
                auto tuple = "(" + paramName.append(", ")
                        .append(sizeRetName)
                        .append(")");
                auto decoderName = "decode_" + uCons->getParam()->getUType()->getTypeName();
                auto decodeUT = new DoStatement;
                decodeUT->bind = tuple;
                decodeUT->expr = decoderName.append(" ")
                        .append(codePrefix + to_string(codeCnt - 1));
                ret->push_back(decodeUT);
                //local length is not fixed
                tokenLength = -1;
            }
            //consume these token
            if (tokenLength != -1) {
                auto skip = new DoStatement;
                auto previous = codePrefix + to_string(codeCnt - 1);
                auto bindName = codePrefix + to_string(codeCnt++);
                _generateSkipN(skip, bindName, previous, to_string(tokenLength));
                lengthCnt += tokenLength;
                ret->push_back(skip);
            } else {
                //local length is not fixed
                auto skip = new DoStatement;
                auto previous = codePrefix + to_string(codeCnt - 1);
                auto bindName = codePrefix + to_string(codeCnt++);
                //variable length
                _generateSkipN(skip, bindName, previous, sizePrefix + to_string(sizeCnt - 1));
                ret->push_back(skip);
            }
        }
        //build the result string
        stringstream retValueStream;
        retValueStream << "OK ((";
        retValueStream << constructorName;

        for (auto param:definition->getUTypeParams()) {
            retValueStream << " ";
            retValueStream << param->getParamName();
        }

        for (auto param:definition->getBuiltInParams()) {
            retValueStream << " ";
            auto &varName = param->getParamName();
            retValueStream << "(" << varName << ")";
//            BuiltInConstructor cons(varName, varName + LENGTH_EVIDENCE_SUFFIX, param->getBuiltInType()->getWidth());
//            retValueStream << cons.toString();
        }
        
        retValueStream << "), ";
        retValueStream << to_string(lengthCnt);
        for (int i = 0; i < sizeCnt; i++) {
            retValueStream << " + ";
            retValueStream << sizePrefix + to_string(i);
        }
        retValueStream << ")";
        ret->push_back(new Statement(retValueStream.str()));
        for (int i = 0; i < assertionCnt; i++) {
            ret->push_back(new Statement("else Error(msg\"impossible\")"));
        }
        return ret;
    }


    vector<Statement *> *generateDecoderBody(const string &varName, vector<pair<string, ir::Definition *>> &variants) {
        auto ret = new vector<Statement *>;
        for (auto &nameDef: variants) {
            auto bpName = nameDef.first + "_bp";
            auto branch = new IfThenElse;
            branch->condition = bpName + " bin";
            auto decoderBody = getDecoderBodyForSingleDefinition(nameDef.first, nameDef.second);
            branch->thenStmts.insert(branch->thenStmts.end(), decoderBody->begin(), decoderBody->end());
            delete decoderBody;
            ret->push_back(branch);
        }
        ret->push_back(new ErrorStmt("Unsupported " + varName));
        return ret;
    }

    string Decoder::generateDecoder() {
        //initialize
        ProgramDefinition funcDef;
        funcDef.name = "decode_" + variantsName;
        Parameter param;
        param.name = "bin";
        funcDef.params.push_back(&param);
        funcDef.retValue = "res (" + variantsName + "*nat)";
        //prelude
        // auto toBits = new LetStatement;
        // toBits->bind = "bin";
        // toBits->expr = "bytes_to_bits_opt " + param.name;
        // funcDef.body.push_back(toBits);
        //generate body
        auto body = generateDecoderBody(variantsName, variants);
        funcDef.body.insert(funcDef.body.end(), body->begin(), body->end());
        delete body;
        sout << funcDef.toString();
        for_each(funcDef.body.begin(), funcDef.body.end(), [](Statement *s) -> void { delete s; });
        return sout.str();
    }
}