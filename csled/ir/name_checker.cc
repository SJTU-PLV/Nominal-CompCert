//
// Created by 徐翔哲 on 12/03/2020.
//

#include "name_checker.hh"
#include "../parser/ast.hh"
#include <set>
#include <iostream>
#include <cassert>

using namespace std;

inline static void unimplement() {
    assert(false);
}

const vector<string> *currentAids;

template<class T>
inline static T *find(map<string, T *> from, const string &key) {
    auto result = from.find(key);
    if (from.cend() == result) {
        return nullptr;
    } else {
        return result->second;
    }
}

template<class T>
inline static T *find(multimap<string, T *> from, const string &key) {
    auto result = from.find(key);
    if (from.cend() == result) {
        return nullptr;
    } else {
        return result->second;
    }
}

inline static bool find(set<string> from, const string &key) {
    auto result = from.find(key);
    if (from.cend() == result) {
        return false;
    } else {
        return true;
    }
}

set<string> builtIns = {"u2", "u3", "u32"};

bool preprocessor::NameChecker::visit(ast::ASTNode &node) {
    unimplement();
    return false;
}

bool preprocessor::NameChecker::visit(ast::TopDef &node) {
    unimplement();
    return false;
}

bool preprocessor::NameChecker::visit(ast::Name &node) {
    unimplement();
    return false;
}

bool preprocessor::NameChecker::visit(ast::Num &node) {
    unimplement();
    return false;
}

bool preprocessor::NameChecker::visit(ast::Token &node) {
    auto *alreadyInToken = find(this->nameTokenMap, node.getTokenName());
    auto *alreadyInField = find(this->nameFieldMap, node.getTokenName());
    auto *alreadyInUType = find(this->nameKlassMap, node.getTokenName());
    if (alreadyInToken != nullptr || alreadyInField != nullptr || alreadyInUType != nullptr) {
        cerr << "Duplicated token named: " << node.getTokenName() << endl;
        this->hasError = true;
    } else {
        this->nameTokenMap.insert({node.getTokenName(), &node});
    }

    return false;
}

bool preprocessor::NameChecker::visit(ast::Field &node) {
    if (find(this->nameTokenMap, node.getTokenName()) == nullptr) {
        this->undefinedName.insert(node.getTokenName());
    }
    auto *alreadyInToken = find(this->nameTokenMap, node.getFieldName());
    auto *alreadyInField = find(this->nameFieldMap, node.getFieldName());
    auto *alreadyInUType = find(this->nameKlassMap, node.getTokenName());
    if (alreadyInField != nullptr || alreadyInToken != nullptr || alreadyInUType != nullptr) {
        cerr << "Duplicated field named: " << node.getFieldName() << endl;
        this->hasError = true;
    } else {
        this->nameFieldMap.insert({node.getFieldName(), &node});
    }
    return false;
}

bool preprocessor::NameChecker::visit(ast::ConstraintBase &node) {
    unimplement();
    return false;
}

bool preprocessor::NameChecker::visit(ast::ConstraintBase::ConstraintRef &node) {
    unimplement();
    return false;
}

bool preprocessor::NameChecker::visit(ast::ConstraintBase::NameRef &node) {
    undefinedName.insert(node.getName());
    return false;
}

bool preprocessor::NameChecker::visit(ast::ConstraintBase::ConstRef &node) {
    return false;
}

bool preprocessor::NameChecker::visit(ast::ConjConstraint &node) {
    return true;
}

bool preprocessor::NameChecker::visit(ast::SemiConstraint &node) {
    return true;
}

bool preprocessor::NameChecker::visit(ast::EQConstraint &node) {
    return true;
}

bool preprocessor::NameChecker::visit(ast::NEConstraint &node) {
    return true;
}

bool preprocessor::NameChecker::visit(ast::NamedConstraint &node) {
    unimplement();
    return false;
}

bool preprocessor::NameChecker::visit(ast::Param &node) {
    unimplement();
    return false;
}

bool preprocessor::NameChecker::visit(ast::ParamList &node) {
    return true;
}


bool preprocessor::NameChecker::visit(ast::UType &node) {
    unimplement();
//    //do not check utype names because utype allows multi-define
//    if (find(this->nameInstrMap, node.getTypeName()) != nullptr
//        || find(this->nameFieldMap, node.getTypeName()) != nullptr
//        || find(this->nameTokenMap, node.getTypeName()) != nullptr) {
//        cerr << "UType name conflict with others " << node.getTypeName() << endl;
//        this->hasError = true;
//    } else {
//        this->nameKlassMap.insert({node.getTypeName(), &node});
//    }
//    this->updateParamNames(&node.getParamList());
    return true;
}

bool preprocessor::NameChecker::visit(ast::Instruction &node) {
    unimplement();
//    if (find(this->nameInstrMap, node.getInstrName()) != nullptr
//        || find(this->nameFieldMap, node.getInstrName()) != nullptr
//        || find(this->nameTokenMap, node.getInstrName()) != nullptr
//        || find(this->nameKlassMap, node.getInstrName()) != nullptr) {
//        cerr << "Duplicated instruction name " << node.getInstrName() << endl;
//        this->hasError = true;
//    } else {
//        this->nameInstrMap.insert({node.getInstrName(), &node});
//    }
//    this->updateParamNames(&node.getParamList());
    return true;
}

bool preprocessor::NameChecker::visit(ast::Specification &node) {
    return true;
}

bool preprocessor::NameChecker::check(ast::Specification *spec) {
    spec->accept(*this);
    set<string> stillUndefined;
    for (auto &name: this->undefinedName) {
        if (find(this->nameFieldMap, name) == nullptr
            && find(this->nameTokenMap, name) == nullptr
            && find(this->nameKlassMap, name) == nullptr) {
            stillUndefined.insert(name);
        }
    }
    if (stillUndefined.empty()) {
        return !hasError;
    } else {
        cerr << "The following name(s) is(are) undefined: " << endl;
        for (auto &s: stillUndefined) {
            cerr << s << endl;
        }
    }
    return false;
}

bool preprocessor::NameChecker::visit(ast::SingleSemiConstraint &node) {
    node.getLhs().accept(*this);
    return false;
}

bool preprocessor::NameChecker::visit(ast::ClsConstraint &node) {
    if (currentAids->size() < node.getIndex()) {
        cerr << "Cls index out of bound" << endl;
    } else {
        undefinedName.insert((*currentAids)[node.getIndex() - 1]);
    }
    return false;
}

bool preprocessor::NameChecker::visit(ast::FldConstraint &node) {
    if (currentAids->size() < node.getIndex()) {
        cerr << "Fld index out of bound" << endl;
    } else {
        undefinedName.insert((*currentAids)[node.getIndex() - 1]);
    }
    return false;
}

bool preprocessor::NameChecker::visit(ast::Constructor &node) {
    currentAids = &node.getAids();
    node.getPattern().accept(*this);
    return false;
}

bool preprocessor::NameChecker::visit(ast::Klass &node) {
    this->nameKlassMap.insert({node.getKlassName(), &node});
    for (auto cons:node.getConstructors()) {
        cons->accept(*this);
    }
    return false;
}
