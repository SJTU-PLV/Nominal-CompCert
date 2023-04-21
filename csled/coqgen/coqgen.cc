#include "coqgen.hh"

//
// Created by 徐翔哲 on 12/22/2020.
//

#include "coqgen.hh"
#include "bp_printer.hh"
#include "proof_condition_printer.hh"
#include <string>
#include <iostream>
#include <vector>
#include <fstream>
#include <algorithm>
#include "type_printer.hh"
#include "encoder.hh"
#include "decoder.hh"
#include "spec_printer.hh"
#include "enc_consistency_printer.hh"
#include "dec_consistency_printer.hh"
#include "bf_true_printer.hh"
#include "soundness_printer.hh"
#include <cassert>
#include <utility>

using namespace std;

namespace coq {


    string writeField(const ir::BitField &bitField) {
        string functionName = "write_" + bitField.getName();
        string tokenBits = bitField.getToken()->getTokenName();
        string fieldValue = bitField.getName() + "_value";
        Parameter tokenParam = {tokenBits, "bits"};
        Parameter bitsParam = {fieldValue, "bits"};
        Definition def;
        def.name = functionName;
        def.params.push_back(&tokenParam);
        def.params.push_back(&bitsParam);
        def.retValue = "bits";
        // LetStatement tokenBitsStmt(tokenByte + "_bits", "bytes_to_bits_opt[" + tokenByte + "]");
        // def.body.push_back(&tokenBitsStmt);
        // string tokenBits = tokenBitsStmt.bind;
        // little endian: bitField.getEnd is the starting offset
        int right = bitField.getToken()->getTokenWidth() - 1 - bitField.getBegin();
        int left = bitField.getEnd();
        stringstream retString;
        if (left != 0) {
            retString << ParenthesisExpression(
                    ListFirstN(tokenBits, left).toString()
            ).toString() + "++";
        }
        retString << fieldValue;
        if (right != 0) {
            int shouldSkip = bitField.getToken()->getTokenWidth() - right;
            retString << "++" << ParenthesisExpression(
                    ListSkipN(tokenBits, shouldSkip).toString()
            ).toString();
        }
        Statement retStmt(retString.str());
        def.body.push_back(&retStmt);
        return def.toString();
    }

    string readField(const ir::BitField &bitField) {
        string functionName = "read_" + bitField.getName();
        string tokenBits = bitField.getToken()->getTokenName();
        Parameter tokenParam = {tokenBits, "bits"};
        Definition def;
        def.name = functionName;
        def.params.push_back(&tokenParam);
        def.retValue = "bits";
        // LetStatement tokenBitsStmt(tokenByte + "_bits", "bytes_to_bits_opt[" + tokenByte + "]");
        // def.body.push_back(&tokenBitsStmt);
        // string tokenBits = tokenBitsStmt.bind;
        int left = bitField.getEnd();
        string list;
        if (left != 0) {
            list = ParenthesisExpression(
                    ListSkipN(tokenBits, left).toString()
            ).toString();
        } else {
            list = tokenBits;
        }
        stringstream retString;
        if (bitField.getBegin() != bitField.getToken()->getTokenWidth() - 1) {
            retString << ListFirstN(list, bitField.getWidth()).toString();
        } else {
            retString << list;
        }
        Statement retStmt(retString.str());
        def.body.push_back(&retStmt);
        return def.toString();
    }

    // unused
    string readWriteFieldConsistent(const ir::BitField &bitField) {
        Lemma lemma;
        lemma.name = "read_write_" + bitField.getName();
        stringstream body;
        body << "forall token field," << endl
             << "length field = " << bitField.getWidth() << "-> " << endl
             << "read_" << bitField.getName() << " (write_" << bitField.getName() << " token field) = field.";
        lemma.body = body.str();
        stringstream proof;
        proof << "intros token field HL;"
              << "destr_byte token; destr_list field;"
              << "unfold read_" << bitField.getName() << ";"
              << "unfold write_" << bitField.getName() << ";"
              << "repeat everything." << endl
              << "Qed.";
        lemma.proof = proof.str();
        return lemma.toString();
    }

    void CoqPrinter::generateFixLength() {
        const int INT_WIDTH = 32;
        for (auto &nameBF:nameBFMap) {
            if (nameBF.second->isSubField()) {
                sout << writeField(*nameBF.second) << endl;
                sout << readField(*nameBF.second) << endl;
                // sout << readWriteFieldConsistent(*nameBF.second) << endl;
            }
        }

        sout << endl;
        // sout << "Hint Resolve";
        // for (auto &nameBF:nameBFMap) {
        //     if (nameBF.second->isSubField()) {
        //         sout << " read_write_" << nameBF.first;
        //     }
        // }
        // sout << ":bitfields." << endl;
        sout << "Hint Unfold";
        for (auto &nameBF:nameBFMap) {
            if (nameBF.second->isSubField()) {
                sout << " read_" << nameBF.first;
                sout << " write_" << nameBF.first;
            }
        }
        sout << ":bitfields." << endl;
    }


    void CoqPrinter::generateListProof() {
        string proof = "simpl; goOver; auto. Qed.";
        for (auto &nameUType:this->irNameUTypeMap) {
            auto utName = nameUType.first;
            int i = 0;
            string list_name = utName + "_bp_list";
            for (auto def:nameUType.second->getDefinitions()) {
                Lemma inlist;
                inlist.name = utName + "_bp_in_list" + to_string(i);
//FIXME                string bp_name = utName + to_string(i) + "_bp";
                string bp_name = def->getName() + "_bp";
                inlist.body = "In " + bp_name + " " + list_name + ".";
                inlist.proof = proof;
                sout << inlist.toString() << endl;
                ++i;
            }
        }

    }

    static string instruction_name = "Instruction";

    void CoqPrinter::generate_Enc_Consistency() {
        ifstream imports("coqgen/texts/consistency_import.txt"), axioms("coqgen/texts/enc_consistency_pre.txt");
        char buffer[510];
        while (imports.good()) {
            imports.getline(buffer, 500);
            encproof << buffer << endl;
        }
        while (axioms.good()) {
            axioms.getline(buffer, 500);
            encproof << buffer << endl;
        }
        encproof << endl;

        //generate non-instruction consistency proof
        ir::UType *instr = nullptr;
        string instr_name;
        for (auto &nameUType:irNameUTypeMap) {
            auto name = nameUType.first;
            if (name == instruction_name) {
                instr = nameUType.second;
                instr_name = name;
                continue;
            }
            //wait to fix
            int i = 0;
            vector<pair<string, ir::Definition *>> defs;
            for (auto def:nameUType.second->getDefinitions()) {
                //auto defName = name + to_string(i++);
                auto defName = def->getName();
                defs.emplace_back(defName, def);
            }
            auto enc = EncConsistency(nameUType.second->getTypeName(), defs, false);
            encproof << enc.generateConform() << endl
                     << enc.generateOrth() << endl
                     << enc.generateEncConsistency() << endl
                     << enc.generatePreserve() << endl;
                     // << enc.generateEncLen() << endl << endl;
        }
        assert(instr);
        vector<pair<string, ir::Definition *>> defs;
        int i = 0;
        for (auto def:instr->getDefinitions()) {
            //auto defName = instr_name + to_string(i++);
            auto defName = def->getName();
            defs.emplace_back(defName, def);
        }
        auto enc = EncConsistency(instr_name, defs, true);
        encproof << enc.generateConform() << endl
                 << enc.generateOrth() << endl
                 << enc.generateEncConsistency() << endl;
    }

    void CoqPrinter::generate_Dec_Consistency() {
        ifstream imports("coqgen/texts/consistency_import.txt"), axioms("coqgen/texts/dec_consistency.txt");
        char buffer[510];
        while (imports.good()) {
            imports.getline(buffer, 500);
            decproof << buffer << endl;
        }
        while (axioms.good()) {
            axioms.getline(buffer, 500);
            decproof << buffer << endl;
        }
        decproof << endl;
        //generate non-instruction consistency proof
        ir::UType *instr = nullptr;
        string instr_name;
        for (auto &nameUType:irNameUTypeMap) {
            auto name = nameUType.first;
            if (name == instruction_name) {
                instr = nameUType.second;
                instr_name = name;
                continue;
            }
            //wait to fix
            int i = 0;
            vector<pair<string, ir::Definition *>> defs;
            for (auto def:nameUType.second->getDefinitions()) {
                //auto defName = name + to_string(i++);
                auto defName = def->getName();
                defs.emplace_back(defName, def);
            }
            auto dec = DecConsistency(nameUType.second->getTypeName(), defs, false);
            decproof << dec.generateConsistency() << endl
                     << dec.generateGtLen() << endl;
        }
        assert(instr);
        vector<pair<string, ir::Definition *>> defs;
        int i = 0;
        for (auto def:instr->getDefinitions()) {
            //auto defName = instr_name + to_string(i++);
            auto defName = def->getName();
            defs.emplace_back(defName, def);
        }
        auto dec = DecConsistency(instr_name, defs, true);
        decproof << dec.generateConsistency() << endl;
    }


    void CoqPrinter::generate_BFtrue() {
        ifstream imports("coqgen/texts/BFtrue_import.txt"), axioms("coqgen/texts/bf_true_pre.txt");;
        char buffer[510];
        while (imports.good()) {
            imports.getline(buffer, 500);
            bftrue << buffer << endl;
        }
        while (axioms.good()) {
            axioms.getline(buffer, 500);
            bftrue << buffer << endl;
        }
        bftrue << endl;
        //generate non-instruction consistency proof
        ir::UType *instr = nullptr;
        string instr_name;
        for (auto &nameUType:irNameUTypeMap) {
            auto name = nameUType.first;
            if (name == instruction_name) {
                instr = nameUType.second;
                instr_name = name;
                continue;
            }
            //wait to fix
            int i = 0;
            vector<pair<string, ir::Definition *>> defs;
            for (auto def:nameUType.second->getDefinitions()) {
                //auto defName = name + to_string(i++);
                auto defName = def->getName();
                defs.emplace_back(defName, def);
            }
            auto bf = BFTrue(nameUType.second->getTypeName(), defs, false);
            bftrue << bf.generateBptrue() << endl << endl;
            //<<bf.generateOrth()<<endl;
        }
        assert(instr);
        vector<pair<string, ir::Definition *>> defs;
        int i = 0;
        for (auto def:instr->getDefinitions()) {
            //auto defName = instr_name + to_string(i++);
            auto defName = def->getName();
            defs.emplace_back(defName, def);
        }
        auto bf = BFTrue(instr_name, defs, true);
        bftrue << bf.generateBptrue() << endl << endl;
        // <<bf.generateOrth()<<endl;
    }


    //unfold bp hint
    void CoqPrinter::generateBpHintdb() {
        for (auto &nameUType:this->irNameUTypeMap) {
            string hint = "Hint Unfold ";
            auto utName = nameUType.first;

            for (auto def:nameUType.second->getDefinitions()) {
                hint += def->getName() + "_bp ";
            }

            hint += ":" + nameUType.first + "_bpdb.";
            sout << endl << hint << endl;
        }
    }

    void CoqPrinter::generateString() {
        ifstream imports("coqgen/texts/imports.txt"), scopes("coqgen/texts/scopes.txt"), axioms(
                "coqgen/texts/axioms.txt");
        char buffer[510];
        while (imports.good()) {
            imports.getline(buffer, 500);
            sout << buffer << endl;
        }
        while (scopes.good()) {
            scopes.getline(buffer, 500);
            sout << buffer << endl;
        }
        while (axioms.good()) {
            axioms.getline(buffer, 500);
            sout << buffer << endl;
        }

        generateFixLength();
//        generateInstrBp();
//        generateUTypeBp();

        ifstream pcIn("coqgen/texts/proof_condition_imports.txt");
        ofstream pcOut("generated/VerificationCondition.v");
        while (pcIn.good()) {
            pcIn.getline(buffer, 500);
            pcOut << buffer << endl;
        }
        ProofConditionPrinter proofConditionPrinter(this->irNameUTypeMap);
        pcOut << proofConditionPrinter.printProofCondition();

        //generate unfold hint for bp
        generateBpHintdb();
        //add generate in_list proof
        generateListProof();

        //prepare for soundness
        ifstream soundnessIn("coqgen/texts/soundness_imports.txt"),
                soundnessPre("coqgen/texts/soundness_pre.txt");
        ofstream soundnessRet("generated/Soundness.v");

        while (soundnessIn.good()) {
            soundnessIn.getline(buffer, 500);
            soundnessRet << buffer << endl;
        }

        while (soundnessPre.good()) {
            soundnessPre.getline(buffer, 500);
            soundnessRet << buffer << endl;
        }

        ofstream specOut("generated/RelSpec.v");
        ifstream specIn("coqgen/texts/spec_imports.txt");
        while (specIn.good()) {
            specIn.getline(buffer, 500);
            specOut << buffer << endl;
        }

        for (const auto &nameUType:irNameUTypeMap) {
            auto name = nameUType.first;
            int i = 0;
            vector<pair<string, ir::Definition *>> defs;
            for (auto def:nameUType.second->getDefinitions()) {
//                auto defName = name + to_string(i++);
                auto defName = def->getName();
                defs.emplace_back(defName, def);
            }

            TypePrinter typePrinter(nameUType.second->getTypeName(), defs);
            sout << typePrinter.generateType();
            auto enc = Encoder(nameUType.second->getTypeName(), defs);
            sout << enc.generateEncoder() << endl;
            auto dec = Decoder(nameUType.second->getTypeName(), defs);
            sout << dec.generateDecoder() << endl;
            auto spec = SpecPrinter(defs, nameUType.second->getTypeName(), nameBFMap);
            specOut << spec.generateSpecs() << endl;
            specOut.flush();

            auto sound = Soundness(defs, nameUType.second->getTypeName(), nameBFMap, spec.getTokenNameBfMap());
            // TODO: add a special case for ecall?
            soundnessRet << sound.generateSoundness() << endl;
            soundnessRet.flush();
        }

        ifstream soundnessAfter("coqgen/texts/soundness_after.txt");
        while (soundnessAfter.good()) {
            soundnessAfter.getline(buffer, 500);
            soundnessRet << buffer << endl;
        }


#ifdef DEBUG
        for (auto &nameInst:irNameInstrMap) {
            sout << nameInst.first << endl;
            auto bps = generateBitPattern(nameInst.second->getDefinition());
            for (const auto &bp:*bps) {
                if (bp.relation == ir::EQ) {
                    sout << "EQ:";
                } else {
                    sout << "NE:";
                }
                sout << endl;
                sout << '\t';
                for (auto b:bp.mask) {
                    sout << b;
                }
                sout << endl;
                sout << '\t';
                for (auto b:bp.pattern) {
                    sout << b;
                }
                sout << endl;

            }
            delete bps;
        }

#endif

    }


    string Statement::toString() {
        return this->anything;
    }


    string Definition::toString() {
        auto &definition = *this;
        stringstream os;
        os << "Definition " << definition.name;
        for (auto &param: definition.params) {
            os << " " << param->toString() << " ";
        }
        if (!definition.retValue.empty()) {
            os << ": " << definition.retValue;
        }
        os << " :=";
        for (auto &stmt: definition.body) {
            os << endl << '\t' + stmt->toString();
        }
        os << "." << endl;
        return os.str();
    }

    string LetStatement::toString() {
        return "let " + this->bind + " := " + this->expr + " in";
    }


    string InductiveType::toString() {
        stringstream ret;
        ret << "Inductive " << typeName << ": Type :=";
        for (auto arm:constructors) {
            ret << endl;
            ret << "| ";
            ret << arm->toString();
        }
        ret << "." << endl;
        return ret.str();
    }

    string MatchArm::toString() {
        stringstream ret;
        ret << constructor;
        for (auto &param:params) {
            ret << " ";
            ret << param;
        }
        ret << " => ";
        bool first = true;
        for (auto &stmt:stmts) {
            if (first) {
                first = false;
            } else {
                ret << endl;
            }
            ret << stmt->toString();
        }
        return ret.str();
    }

    MatchArm::~MatchArm() {
        for (auto stmt:stmts) {
            delete stmt;
        }
    }

    string MatchStatement::toString() {
        stringstream ret;
        ret << "match " << variable << " with";
        for (auto arm:branches) {
            ret << endl;
            ret << "| " << arm->toString();
        }
        ret << endl;
        ret << "end";
        return ret.str();
    }

    MatchStatement::~MatchStatement() {
        for (auto arm:branches) {
            delete arm;
        }
    }

    string DoStatement::toString() {
        return "do " + bind + " <- " + expr + ";";
    }

    IfThenElse::~IfThenElse() {
        for (auto s:thenStmts) {
            delete s;
        }
        for (auto s: elseStmts) {
            delete s;
        }
    }

    string IfThenElse::toString() {
        stringstream ret;
        ret << "if " << condition << " then" << endl;
        for (auto s:thenStmts) {
            ret << s->toString() << endl;
        }
        ret << "else" << endl;
        for (auto s:elseStmts) {
            ret << s->toString() << endl;
        }
        return ret.str();
    }

    string ErrorStmt::toString() {
        return "Error(msg\"" + msg + "\")";
    }

    string BuiltInConstructor::toString() {
        stringstream ret;
        ret << "{|data" << width << " := " << varName << ";"
            << "bl" << width << " := " << evidence << " |}";
        return ret.str();
    }

    string ProgramDefinition::toString() {
        return "Program " + Definition::toString();
    }
}