//
// Created by 徐翔哲 on 04/21/2021.
//

#include "soundness_printer.hh"
#include "coqgen.hh"
#include "util.hh"

namespace coq {
    typedef vector<pair<string, ir::Definition *>> var_defs_t;
    bool fullyQualified = false;

    bool _isVariantFullyQualified(var_defs_t *variants) {
        for (auto &nameDef:*variants) {
            if (!nameDef.second->isFullyQualified()) {
                return false;
            }
        }
        return true;
    }

    string sigAndPrologue(const string &variantsName) {
        Lemma lemma;
        lemma.name = "encode_" + variantsName + "_sound";
        if (fullyQualified) {
            stringstream body;
            body << "forall i lst," << endl;
            body << "encode_" << variantsName << " i = OK lst" << endl;
            body << "-> " << variantsName << "_spec lst i.";
            lemma.body = body.str();
            lemma.proof = "intros i lst HEncode. \n"
                          "induction i; simpl.";
        } else {
            stringstream body;
            body << "forall i input lst," << endl;
            body << "encode_" << variantsName << " i input = OK lst" << endl;
            body << "-> " << variantsName << "_spec (bytes_to_bits_opt lst) i.";
            lemma.body = body.str();
            lemma.proof = "intros i input lst HEncode. \n"
                          "induction i.";

        }

        return lemma.toString();
    }

    string destrInput() {
        stringstream ret;
        ret << "destr_byte input." << endl;
        ret << "rename b7 into inb7." << endl;
        ret << "rename b6 into inb6." << endl;
        ret << "rename b5 into inb5." << endl;
        ret << "rename b4 into inb4." << endl;
        ret << "rename b3 into inb3." << endl;
        ret << "rename b2 into inb2." << endl;
        ret << "rename b1 into inb1." << endl;
        ret << "rename b0 into inb0." << endl;
        return ret.str();
    }

    string solveBuiltinParams(ir::Definition *definition) {
        stringstream ret;
        for (auto builtInParam:definition->getBuiltInParams()) {
            ret << "destr_para_name_type " << builtInParam->getParamName()
                << " " << builtInParam->getParamName()
                << " " << builtInParam->getBuiltInType()->toString()
                << " H" << builtInParam->getParamName()
                << "." << endl;
        }
        return ret.str();
    }

    int _countNeqChecks(ir::SemiConstraint *cons) {
        int cnt = 0;
        for (auto &conj:cons->getConstraints()) {
            for (auto ccons:conj->getCConstraints()) {
                if (ccons->getRelation() == ir::NE) {
                    cnt++;
                }
            }
        }
        return cnt;
    }

    vector<int> klassMonadIdx;

    int _countMonad(ir::SemiConstraint *cons) {
        klassMonadIdx.clear();
        int cnt = 0;
        for (auto &conj:cons->getConstraints()) {
            for (auto &pcons:conj->getPConstraints()) {
                if (pcons->getParam()->getBuiltInType()->getWidth() >= 8) {
                    cnt++;
                }
            }
            for (auto &ucons:conj->getUtConstraints()) {
                klassMonadIdx.insert(klassMonadIdx.begin(), cnt++);
            }
        }

        return cnt;
    }


    string solveHEncode(ir::Definition *definition) {
        stringstream ret;
        ret << "simpl in HEncode." << endl;
        int checkNum = _countNeqChecks(&definition->getConstraints());
        for (int i = 0; i < checkNum; i++) {
            ret << "destruct builtin_eq_dec eqn:EQB" << i
                << " in HEncode; [inversion HEncode|]." << endl;
        }
        int monadNum = _countMonad(&definition->getConstraints());
        ret << "simpl in HEncode. try (monadInv HEncode ";
        static const char *name = " 10234567";
        static const char *varName = " 01234567";
        for (int i = 0; i < monadNum; i++) {
            ret << ";";
            ret << " try rename EQ" << name[i] << " into HEnc" << i<<";"<<endl;
            ret << " try rename x" << varName[i] << " into xx" << i << endl;
        }
        ret << ")." << endl;
        return ret.str();
    }

    string destrBuiltInParams(ir::Definition *definition) {
        stringstream ret;
        const char *name = " 0123456";
        for (auto builtInParam:definition->getBuiltInParams()) {
            int width = builtInParam->getBuiltInType()->getWidth();
            if (width > 8) {
                continue;
            }
            ret << "destr_list  " << builtInParam->getParamName() << "." << endl;
            for (int i = 0; i < width; i++) {
                ret << "rename b" << name[i] << " into "
                    << builtInParam->getParamName() << width - 1 - i << "." << endl;
            }
            ret << "try clear HLTail." << endl;
        }
        return ret.str();
    }

    string _getBitsString(int begin, int end, const string &prefix) {
        stringstream ret;
        ret << "[";
        const string &name = prefix;
        bool first = true;
        for (int i = begin; i >= end; i--) {
            if (first) {
                first = false;
            } else {
                ret << ";";
            }
            ret << name << i;
        }
        ret << "]";
        return ret.str();
    }

    string _try_solveBFFromConstraint(const ir::ConjConstraint *conj, ir::BitField *bf) {
        for (auto ccons: conj->getCConstraints()) {
            if (ccons->getToConstrain()->getName() == bf->getName() && ccons->getRelation() == ir::EQ) {
                return util::_valueToBits(ccons->getValue()->getValue(), bf->getWidth());
            }
        }
        for (auto pcons: conj->getPConstraints()) {
            if (pcons->getToConstrain()->getName() == bf->getName()) {
                string name = pcons->getParam()->getParamName();
                int width = bf->getWidth();
                return name;
                // return _getBitsString(width - 1, 0, name);
            }
        }
        return "";
    }

    string _solveBFFromConstraint(const ir::ConjConstraint *conj, ir::BitField *bf, const string &inbPrefix = "inb") {
        auto ret = _try_solveBFFromConstraint(conj, bf);
        if (ret.empty()) {
            return _getBitsString(bf->getBegin(), bf->getEnd(), inbPrefix);
        } else {
            return ret;
        }
    }

    string solveExistence(ir::Definition *definition,
                          const map<string, vector<ir::BitField *> *> &tokenBFs,
                          const map<string, ir::BitField *> &nameBFMap) {
        stringstream ret;
        auto constraint = definition->getConstraints();
        for (auto &conj:constraint.getConstraints()) {
            const ast::Token *currentToken = nullptr;
            if (!conj->getCConstraints().empty()) {
                currentToken = conj->getCConstraints()[0]->getToConstrain()->getToken();
            } else if (!conj->getPConstraints().empty()) {
                currentToken = conj->getPConstraints()[0]->getToConstrain()->getToken();
            } else {
                //cannot resolve token for the constraint?
                assert(false);
            }
            auto &tokenName = currentToken->getTokenName();
            // TODO: this is a hack. May fail x86 ISA.
            // if (currentToken->getTokenWidth() <= 8) {
            if (true) {
                //first give this token a try
                //token as a field
                auto nameToken = nameBFMap.find(tokenName);
                if (nameToken != nameBFMap.end()) {
                    auto tokenRet = _try_solveBFFromConstraint(conj, nameToken->second);
                    if (!tokenRet.empty()) {
                        ret << "exists " << tokenRet << "." << endl;
                        continue;
                    }
                }
                //then try the subfields of this token
                auto nameBFs = tokenBFs.find(tokenName);
                if (nameBFs != tokenBFs.end()) {
                    auto bfs = nameBFs->second;
                    for (auto &bf: *bfs) {
                        ret << "exists " << _solveBFFromConstraint(conj, bf) << "." << endl;
                    }
                }

            } else {
                //currently, there might only be a pcons
                ret << "exists " << conj->getPConstraints()[0]->getParam()->getParamName() << "." << endl;
            }
            if (!conj->getUtConstraints().empty()) {
                const string &typeName = conj->getUtConstraints()[0]->getParam()->getUType()->getTypeName();
                ret << "exists (bytes_to_bits_opt " << typeName << "_instance)." << endl;
            }
        }
        return ret.str();
    }

    string solvePossibleHexValue(ir::Definition *definition) {
        stringstream ret;
        for (const auto &cons:definition->getConstraints().getConstraints()) {
            for (const auto &ccons: cons->getCConstraints()) {
                int value = ccons->getValue()->getValue();
                ret << "try try_hexize_value " << value << "%Z." << endl;
            }
        }
        ret << "try try_hexize_value " << 0 << "%Z." << endl;
        return ret.str();
    }

    void _set_touch_bits(bool tb[], const vector<ir::Definition *> &variants) {
        for (auto &nameDef:variants) {
            //first conjunction
            auto conj = nameDef->getConstraints().getConstraints()[0];
            for (auto &paraCon:conj->getPConstraints()) {
                assert(paraCon->getToConstrain()->getWidth() <= 8);
                int begin, end;
                begin = paraCon->getToConstrain()->getBegin();
                end = paraCon->getToConstrain()->getEnd();
                for (int i = end; i <= begin; ++i)tb[8 - i - 1] = true;
            }
            for (auto &cCon:conj->getCConstraints()) {
                assert(cCon->getToConstrain()->getWidth() <= 8);
                int begin, end;
                begin = cCon->getToConstrain()->getBegin();
                end = cCon->getToConstrain()->getEnd();
                for (int i = end; i <= begin; ++i)tb[8 - i - 1] = true;
            }
            assert(conj->getUtConstraints().size() == 0);
        }
    }

    string solveKlass(ir::Definition *definition) {
        stringstream ret;
        for (const auto &conj:definition->getConstraints().getConstraints()) {
            for (const auto &ucons:conj->getUtConstraints()) {
                string hypoName = "HEnc" + to_string(klassMonadIdx[klassMonadIdx.size() - 1]);
                klassMonadIdx.pop_back();
                for (const auto &ccons:conj->getCConstraints()) {
                    ret << "hexize_byte_value " << ccons->getValue()->getValue()
                        << "%Z; try rewrite HHex in " << hypoName << "; clear HHex." << endl;
                }
                ret << "hexize_byte_value " << 0
                    << "%Z; try rewrite HHex in " << hypoName << "; clear HHex." << endl;

                ret << "autounfold with bitfields in " << hypoName << "." << endl;
                ret << "repeat simpl_bytes_to_bits_in " << hypoName << "." << endl;
                ret << "simpl in " << hypoName << "." << endl;
                const string &typeName = ucons->getParam()->getUType()->getTypeName();
                auto utype_name = conj->getUtConstraints()[0]->getParam()->getUType()->getTypeName();
                string Enc="encode_"+utype_name;
                string Preserve=Enc+"_preserve";
                ret << "solve_preserve_klass " << Enc+" "+Preserve << "." <<endl;
                //ret << "solve_preserve_" << typeName << "." << endl;
                bool mask[8] = {false};
                _set_touch_bits(mask, ucons->getParam()->getUType()->getDefinitions());
                int touchCnt = 0;
                static const char *name = " 012345678";
                for (int i = 0; i < 8; i++) {
                    if (mask[i]) {
                        ret << "rename x" << name[touchCnt++] << " into inb" << 7 - i << "." << endl;
                    }
                }
                ret << "rename x" << name[touchCnt++] << " into "
                    << typeName << "_instance." << endl;
                ret << "repeat simpl_bytes_to_bits. simpl." << endl;
                ret << "generalize (encode_" << typeName << "_sound _ _ _ " << hypoName << ")." << endl;
                ret << "intros H" << typeName << "." << endl;
                ret << "simpl_bytes_to_bits_in H" << typeName << ".";
            }
        }
        return ret.str();
    }

    string solveInstances(var_defs_t *variants,
                          const map<string, vector<ir::BitField *> *> &tokenBFs,
                          const map<string, ir::BitField *> &nameBFMap) {
        stringstream ret;
        for (auto &nameDef:*variants) {
            ret << endl;
            ret << "(**** " << nameDef.first << " *****)" << endl;
            ret << solveBuiltinParams(nameDef.second);
            if (!fullyQualified) {
                ret << destrInput();
            }
            ret << solveHEncode(nameDef.second);
            ret << " autounfold with bitfields. simpl." << endl;
//             ret << solvePossibleHexValue(nameDef.second) << endl;
// //            ret << "repeat try_hexize_value." << endl;
//             ret << "simpl_bytes_to_bits." << endl;
//             ret << destrBuiltInParams(nameDef.second);
//             ret << endl;
//             ret << "simpl. simpl_bytes_to_bits. simpl." << endl;
//             ret << "repeat rewrite bytes_to_bits_opt_app." << endl;
//             ret << "repeat solve_bits_to_bytes_to_bits." << endl;
//             ret << solveKlass(nameDef.second) << endl;
            ret << "constructor." << endl;
            ret << solveExistence(nameDef.second, tokenBFs, nameBFMap);
            ret << "finalize_soundness." << endl;
        }
        ret << "Qed." << endl;
        return ret.str();
    }


    string Soundness::generateSoundness() {
        fullyQualified = _isVariantFullyQualified(&variants);
        stringstream ret;
        ret << sigAndPrologue(variantsName);
        ret << solveInstances(&variants, this->tokenNameBFMap, this->nameBFMap);
        return ret.str();
    }
}