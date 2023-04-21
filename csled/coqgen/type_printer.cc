//
// Created by 徐翔哲 on 04/19/2021.
//

#include "type_printer.hh"
#include "coqgen.hh"
#include <utility>

namespace coq{
    void cleanMemory(InductiveType &type) {
        for (auto cons:type.constructors) {
            for (auto param:cons->params) {
                delete param;
            }
            delete cons;
        }
    }


    string getInductiveDefinition(const string &varName, vector<pair<string, ir::Definition *>> &variants) {
        InductiveType type;
        type.typeName = varName;
        for (const auto &nameDef:variants) {
            auto &nameOfDefinition = nameDef.first;
            auto arm = new InductiveArm;
            arm->constructorName = nameOfDefinition;
            //the order is VERY important!!!!
            //UT first, then BuiltIn
            for (auto param: nameDef.second->getUTypeParams()) {
                auto *parameter = new Parameter;
                parameter->name = param->getParamName();
                parameter->type = param->getUType()->getTypeName();
                arm->params.push_back(parameter);
            }
            for (auto param:nameDef.second->getBuiltInParams()) {
                auto *parameter = new Parameter;
                parameter->name = param->getParamName();
                auto width = param->getBuiltInType()->getWidth();
                parameter->type = "u" + to_string(width);
                arm->params.push_back(parameter);
            }
            type.constructors.push_back(arm);
        }
        auto ret = type.toString();
        cleanMemory(type);
        return ret;
    }

    static const char *const ELEMENT = "element";


    string getInductiveOpcode(const string &varName, vector<pair<string, ir::Definition *>> &variants) {
        const string suffix = "_op";
        InductiveType type;
        type.typeName = varName + suffix;
        for (const auto &nameDef:variants) {
            auto &nameOfDefinition = nameDef.first;
            auto arm = new InductiveArm;
            arm->constructorName = nameOfDefinition + suffix;
            type.constructors.push_back(arm);
        }
        auto ret = type.toString();
        cleanMemory(type);
        return ret;
    }


    string fromTypesToOpcodes(const string &varName, vector<pair<string, ir::Definition *>> &variants) {
        const string suffix = "_op";
        Definition funcDef;
        MatchStatement matchStmt;
        //initialize
        string typeConstructor = varName;
        funcDef.name = typeConstructor.append("_to").append(suffix);
        string element = ELEMENT;
        funcDef.params.push_back(new Parameter(element, ""));
        matchStmt.variable = element;

        for (const auto &nameDef:variants) {
            auto &nameOfDefinition = nameDef.first;
            auto arm = new MatchArm;
            arm->constructor = nameOfDefinition;
            for (auto p: nameDef.second->getUTypeParams()) {
                arm->params.emplace_back("_");
            }
            for (auto p: nameDef.second->getBuiltInParams()) {
                arm->params.emplace_back("_");
            }
            arm->stmts.push_back(new Statement(nameOfDefinition + suffix));
            matchStmt.branches.push_back(arm);
        }
        funcDef.body.push_back(&matchStmt);
        auto ret = funcDef.toString();
        delete funcDef.params[0];
        return ret;
    }

    string fromOpcodesToBp(const string &varName, vector<pair<string, ir::Definition *>> &variants) {
        const string op = "_op";
        const string bp = "_bp";
        Definition funcDef;
        MatchStatement matchStmt;
        //initialize
        string typeConstructor = varName;
        funcDef.name = typeConstructor.append(op).append("_to").append(bp);
        string element = ELEMENT;
        funcDef.params.push_back(new Parameter(element, ""));
        matchStmt.variable = element;

        for (const auto &nameDef:variants) {
            auto &nameOfDefinition = nameDef.first;
            auto arm = new MatchArm;
            arm->constructor = nameOfDefinition + op;
            arm->stmts.push_back(new Statement(nameOfDefinition + bp));
            matchStmt.branches.push_back(arm);
        }
        funcDef.body.push_back(&matchStmt);
        auto ret = funcDef.toString();
        delete funcDef.params[0];
        return ret;
    }


    string TypePrinter::generateType() {
        stringstream ret;
        auto varName = this->variantsName;
        ret << getInductiveDefinition(varName, this->variants);
        ret << getInductiveOpcode(varName, this->variants);
        ret << fromTypesToOpcodes(varName, this->variants);
        ret << fromOpcodesToBp(varName, this->variants);
        return ret.str();
    }
}