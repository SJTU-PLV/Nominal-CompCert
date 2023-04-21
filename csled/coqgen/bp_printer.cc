//
// Created by 徐翔哲 on 12/23/2020.
//
#include "bp_printer.hh"
#include "coqgen.hh"
#include <string>
#include <iostream>
#include <vector>
#include <fstream>
#include <cassert>


using namespace std;

namespace coq {

    BitPattern _constToBP(BitPattern &base, int begin, ir::ConstConstraint *constraint) {
        auto ret = base;
        auto width = constraint->getLength();
        // field[bfEnd..bfBegin]
        auto bfBegin = constraint->getToConstrain()->getBegin();
        auto bfEnd = constraint->getToConstrain()->getEnd();
        auto value = constraint->getValue()->getValue();
        for (int i = bfEnd; i <= bfBegin; i++) {
            ret.mask[begin + i] = true;
            bool currentBit = (value & 0x1) == 1;
            ret.pattern[begin + i] = currentBit;
            value >>= 1;
        }
        ret.relation = constraint->getRelation();
        return ret;
    }

    vector<BitPattern> *_conjToBP(int *prefixLength, ir::ConjConstraint *constraint) {
        auto ret = new vector<BitPattern>();
        int width = -1;
        if (!constraint->getCConstraints().empty()) {
            width = constraint->getCConstraints()[0]->getLength();
        } else if (!constraint->getPConstraints().empty()) {
            width = constraint->getPConstraints()[0]->getLength();
        }
        if (width == -1) {
            assert(false);
            return ret;
        }
        int begin = *prefixLength;
        BitPattern base;
        for (int i = 0; i < *prefixLength; i++) {
            base.mask.push_back(false);
            base.pattern.push_back(false);
        }
        //append bp
        for (int i = 0; i < width; i++) {
            base.mask.push_back(false);
            base.pattern.push_back(false);
        }
        //apply constraints
        for (auto &cons:constraint->getCConstraints()) {
            auto result = _constToBP(base, begin, cons);
            ret->push_back(result);
        }
        *prefixLength += width;
        return ret;
    }

    vector<BitPattern> *_semiToBP(ir::SemiConstraint *constraint) {
        int prefixLength = 0;
        vector<BitPattern> eqs;
        auto ret = new vector<BitPattern>;
        auto &nes = *ret;
        for (auto &cons:constraint->getConstraints()) {
            if (cons->hasFixLengthPrefix()) {
                auto bps = _conjToBP(&prefixLength, cons);
                for (const auto &bp:*bps) {
                    if (bp.relation == ir::EQ) {
                        eqs.push_back(bp);
                    } else {
                        nes.push_back(bp);
                    }
                }
                delete bps;
            }
            if (!cons->isFixLength()) {
                break;
            }
        }
        BitPattern eqBp;
        eqBp.mask = vector<bool>(false, prefixLength);
        eqBp.pattern = eqBp.mask;
        for (const auto &bp:eqs) {
            eqBp = eqBp | bp;
        }
        eqBp.relation = ir::EQ;
        ret->push_back(eqBp);
        return ret;
    }

    vector<BitPattern> *generateBitPattern(ir::Definition *definition) {
        return _semiToBP(&definition->getConstraints());
    }
}