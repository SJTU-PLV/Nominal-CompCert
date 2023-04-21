//
// Created by 徐翔哲 on 04/24/2021.
//

#include "proof_condition_printer.hh"
#include "bp_printer.hh"
#include "coqgen.hh"

namespace coq {
    void addBitPatternStatements(Definition &funcDef, vector<LetStatement *> &conds,
                                 int i, BitPattern &bp) {
        auto mask = new LetStatement;
        mask->bind = "bmask" + to_string(i);
        mask->expr = "[" + bp.maskString() + "]";
        funcDef.body.push_back(mask);
        auto result = new LetStatement;
        result->bind = "bresult" + to_string(i);
        result->expr = "[" + bp.patternString() + "]";
        funcDef.body.push_back(result);
        auto match = new LetStatement;
        match->bind = "bmatch" + to_string(i);
        string relation = bp.relation == ir::EQ ? "bp_eq" : "bp_neq";
        match->expr = relation + "(bp_and " + mask->bind + " code) " + result->bind;
        funcDef.body.push_back(match);
        conds.push_back(match);
    }

    LetStatement &getLengthStatement(int maxSize) {
        auto length =  to_string(maxSize)+" <=? (length code)";
        LetStatement &blen = *new LetStatement;
        blen.bind = "blen";
        blen.expr = length;
        return blen;
    }

    void getFunctionSignature(Definition &funcDef, Parameter &parameter) {
        string input = "code";
        parameter.name = input;
        funcDef.params.push_back(&parameter);
        funcDef.retValue = "bool";
    }

    int getMaxBpLength(vector<BitPattern> &bps) {
        int maxSize = 0;
        for (auto &bp: bps) {
            auto size = bp.mask.size();
            maxSize = max<int>(size, maxSize);
        }
        return maxSize;
    }



    string generateBptNeq(const string &typeName, vector<string> &bps) {
        vector<string> neqs;
        stringstream ret;
        for (int i = 0; i < bps.size(); i++) {
            for (int k = i + 1; k < bps.size(); k++) {
                Axiom lemmaDef;
                lemmaDef.name = typeName + "_bp_neq" + to_string(i) + "_" + to_string(k);
                lemmaDef.body = "bpt_neq " + bps[i] + " " + bps[k] + ".";
                neqs.push_back(lemmaDef.name);
                ret << lemmaDef.toString();
                ret << endl;
            }
        }
        ret << endl;
        if (neqs.size()!=0) {
            ret << "Hint Resolve";
            for (auto &ne:neqs) {
                ret << " " << ne;
            }
            ret << ":bpneq. " << endl << endl;
        }
        return ret.str();
    }

    string getCoqBpCode(string functionName, vector<BitPattern> *bps) {
        stringstream sout;
        Definition funcDef;
        Parameter parameter;
        funcDef.name = functionName;
        getFunctionSignature(funcDef, parameter);
        int maxSize = getMaxBpLength(*bps);
        vector<LetStatement *> conds;
        //length condition
        auto &blen = getLengthStatement(maxSize);
        funcDef.body.push_back(&blen);
        conds.push_back(&blen);
        //other conditions
        int i = 0;
        for (auto &bp: *bps) {
            addBitPatternStatements(funcDef, conds, i++, bp);
        }
        //the result statement
        stringstream funcRet;
        funcRet << "true";
        for (auto &cond: conds) {
            funcRet << " && " << cond->bind;
        }
        auto stmt = new Statement(funcRet.str());
        funcDef.body.push_back(stmt);
        sout << funcDef.toString();
        for (auto &s:funcDef.body) {
            delete s;
        }
        return sout.str();
    }

    string coq::ProofConditionPrinter::printProofCondition() {
        ofstream smtOut("generated/bp_in_smt.txt");
        for (auto &nameUType:this->irNameUTypeMap) {
            vector<string> bpNames;
            auto utName = nameUType.first;
            int i = 0;

            for (auto def:nameUType.second->getDefinitions()) {
                sout << endl;
                auto bps = generateBitPattern(def);
                assert(!bps->empty());
                //FIXME hard coded name
//                string functionName = utName + to_string(i++) + "_bp";
                string functionName = def->getName() + "_bp";
                bpNames.push_back(functionName);
                sout << getCoqBpCode(functionName, bps);
                for (auto &bp:*bps) {
                    switch (bp.relation) {
                        case ir::EQ:
                            smtOut << "EQ" << endl;
                            break;
                        case ir::NE:
                            smtOut << "NE" << endl;
                            break;
                    }
                    smtOut << "M" << bp.maskStringExtendedTo(120) << endl;
                    smtOut << "V" << bp.patternStringExtendedTo(120) << endl;
                    smtOut << "********" << endl;
                }
                smtOut << "---------" << endl;
            }
            smtOut << "+++++" << utName << "++++++" << endl;

            stringstream bplist;
            bplist << "Definition " + nameUType.first + "_bp_list := [";
            bool first = true;
            int k = 0;
            for (auto def:nameUType.second->getDefinitions()) {
                if (first) {
                    first = false;
                } else {
                    bplist << "; ";
                }
//FIXME                string bpName = utName + to_string(k++) + "_bp";
                string bpName = def->getName() + "_bp";
                bplist << bpName;
            }
            bplist << "]." << endl;
            sout << bplist.str();
            sout << generateBptNeq(nameUType.first, bpNames);
        }
        //            ofstream smt("bp_in_smt.txt");
//            smt << smtOut.str();
//            smt.flush();
        smtOut.flush();
        return sout.str();
    }
}