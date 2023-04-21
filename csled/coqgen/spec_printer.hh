//
// Created by 徐翔哲 on 01/10/2021.
//

#ifndef FRONTEND_SPEC_HH
#define FRONTEND_SPEC_HH


#include "bp_printer.hh"
#include "coqgen.hh"
#include <string>
#include <iostream>
#include <vector>
#include <map>
#include <fstream>
#include "../ir/ir.hh"
#include <utility>

namespace coq {
    class SpecPrinter {
        vector<pair<string, ir::Definition *>> &variants;
        map<string, vector<ir::BitField *>*> tokenNameBFMap;
        const map<string, ir::BitField *> &nameBFMap;
        stringstream sout;
        string variantsName;
    private:
        void preprocess();

    public:
        SpecPrinter(vector<pair<string, ir::Definition *>> &variants, const string &variantsName,
                    const map<string, ir::BitField *> &nameBFMap)
                : variants(variants), variantsName(variantsName), nameBFMap(nameBFMap) {}

        string generateSpecs();

        const map<string, vector<ir::BitField *> *> &getTokenNameBfMap() const {
            return tokenNameBFMap;
        }
    };
}


#endif //FRONTEND_SPEC_HH
