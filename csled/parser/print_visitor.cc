//
// Created by 徐翔哲 on 12/02/2020.
//

#include "print_visitor.hh"
#include "ast.hh"

bool ast::PrintVisitor::visit(ast::ASTNode &node) {
    cout << "WOW it's an ASTNode!" << endl;
    return true;
}

bool ast::PrintVisitor::visit(ast::TopDef &node) {
    cout << "WOW it's a TopDef!" << endl;
    return true;
}

bool ast::PrintVisitor::visit(ast::Name &node) {
    printIdent();
    cout << "AST-Name: " << node.getName() << endl;
    return true;
}

bool ast::PrintVisitor::visit(ast::Num &node) {
    printIdent();
    cout << "AST-Num: " << node.getNum() << endl;
    return true;
}

bool ast::PrintVisitor::visit(ast::Token &node) {
    printIdent();
    cout << "AST-Token: " << endl;
    identCounter++;
    printIdent();
    cout << "Token name: " << node.getTokenName() << endl;
    printIdent();
    cout << "Token width: " << node.getTokenWidth() << endl;
    identCounter--;
    return false;
}

bool ast::PrintVisitor::visit(ast::Field &node) {
    printIdent();
    cout << "AST-Field: " << endl;
    identCounter++;
    printIdent();
    cout << "Field name: " << node.getFieldName() << endl;
    printIdent();
    cout << "Token name: " << node.getTokenName() << endl;
    printIdent();
    cout << "Field range (" << node.getBfBegin() << ":" << node.getBfEnd() << ")" << endl;
    identCounter--;
    return false;
}

bool ast::PrintVisitor::visit(ast::ConstraintBase &node) {
    cout << "WOW it's a ConstraintBase!" << endl;
    return true;
}

bool ast::PrintVisitor::visit(ast::ConstraintBase::ConstraintRef &node) {
    cout << "WOW it's a ConstraintRef!" << endl;
    return true;
}

bool ast::PrintVisitor::visit(ast::ConstraintBase::NameRef &node) {
    printIdent();
    cout << "AST-NameRef: " << node.getName() << endl;
    return true;
}

bool ast::PrintVisitor::visit(ast::ConstraintBase::ConstRef &node) {
    printIdent();
    cout << "AST-ConstRef: " << node.getNumber() << endl;
    return true;
}

bool ast::PrintVisitor::visit(ast::ConjConstraint &node) {
    printIdent();
    cout << "AST-ConjConstraint: &" << endl;
    identCounter++;
    node.getLhs().accept(*this);
    node.getRhs().accept(*this);
    identCounter--;
    return false;
}

bool ast::PrintVisitor::visit(ast::SemiConstraint &node) {
    printIdent();
    cout << "AST-SemiConstraint: ;" << endl;
    identCounter++;
    node.getLhs().accept(*this);
    node.getRhs().accept(*this);
    identCounter--;
    return false;
}

bool ast::PrintVisitor::visit(ast::EQConstraint &node) {
    printIdent();
    cout << "AST-EQConstraint: ==" << endl;
    identCounter++;
    node.getLhs().accept(*this);
    node.getRhs().accept(*this);
    identCounter--;
    return false;
}

bool ast::PrintVisitor::visit(ast::NEConstraint &node) {
    printIdent();
    cout << "AST-NEConstraint: !=" << endl;
    identCounter++;
    node.getLhs().accept(*this);
    node.getRhs().accept(*this);
    identCounter--;
    return false;
}

bool ast::PrintVisitor::visit(ast::NamedConstraint &node) {
    printIdent();
    cout << "AST-NamedConstraint: " <<node.getName()<<endl;
    return true;
}

bool ast::PrintVisitor::visit(ast::Param &node) {
    printIdent();
    cout << "AST-Param: " << node.getName() << " : " << node.getTypeName() << endl;
    return true;
}

bool ast::PrintVisitor::visit(ast::ParamList &node) {
    printIdent();
    cout << "AST-ParamList: "<<endl;
    identCounter++;
    for (auto p:node.getParams()) {
        p->accept(*this);
    }
    identCounter--;
    return false;
}

bool ast::PrintVisitor::visit(ast::UType &node) {
    printIdent();
    cout << "AST-UType: " << node.getTypeName() << endl;
    identCounter++;
    node.getCons().accept(*this);
    node.getParamList().accept(*this);
    identCounter--;
    return false;
}

bool ast::PrintVisitor::visit(ast::Instruction &node) {
    printIdent();
    cout << "AST-Instruction: " << node.getInstrName() << endl;
    identCounter++;
    node.getCons().accept(*this);
    node.getParamList().accept(*this);
    identCounter--;
    return false;
}

bool ast::PrintVisitor::visit(ast::Specification &node) {
    printIdent();
    cout << "AST-Specification: " << endl;
    identCounter++;
    for (auto p: node.getTops()) {
        p->accept(*this);
    }
    identCounter--;
    cout<< "End of print visitor"<<endl;
    return false;
}

bool ast::PrintVisitor::visit(ast::SingleSemiConstraint &node) {
    printIdent();
    cout << "Single Semi Constraint:" << endl;
    identCounter++;
    node.getLhs().accept(*this);
    identCounter--;
    cout << "End of Single Semi Constraint" << endl;
    return false;
}

bool ast::PrintVisitor::visit(ast::ClsConstraint &node) {
    cout << "Cls Constraint: cls %" << node.getIndex() << endl;
    return false;
}

bool ast::PrintVisitor::visit(ast::FldConstraint &node) {
    cout << "Fld Constraint: fld %" << node.getIndex() << endl;
    return false;
}

bool ast::PrintVisitor::visit(ast::Constructor &node) {
    printIdent();
    cout << "Constructor " << node.getConstructorName() << ":" << endl;
    identCounter++;
    printIdent();
    cout << "args: " << "[";
    for (const auto& arg:node.getAids()) {
        cout << " " << arg;
    }
    cout << "]" << endl;
    node.getPattern().accept(*this);
    identCounter--;
    return false;
}

bool ast::PrintVisitor::visit(ast::Klass &node) {
    printIdent();
    cout << "Class " << node.getKlassName() << ":" << endl;
    identCounter++;
    for (auto &con:node.getConstructors()) {
        con->accept(*this);
    }
    identCounter--;
    return false;
}
