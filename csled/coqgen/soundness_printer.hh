//
// Created by 徐翔哲 on 04/21/2021.
//

#ifndef ARTIFACT_SOUNDNESS_PRINTER_HH
#define ARTIFACT_SOUNDNESS_PRINTER_HH

#include "coqgen.hh"
#include <string>
#include <iostream>
#include <vector>
#include <map>
#include <fstream>
#include "../ir/ir.hh"
#include <utility>

namespace coq {

    class Soundness {
        vector<pair<string, ir::Definition *>> &variants;
        map<string, vector<ir::BitField *> *> tokenNameBFMap;
        const map<string, ir::BitField *> &nameBFMap;
        stringstream sout;
        string variantsName;
    private:


    public:
        Soundness(vector<pair<string, ir::Definition *>> &variants, const string &variantsName,
                  const map<string, ir::BitField *> &nameBFMap,
                  const map<string, vector<ir::BitField *> *> tokenNameBFMap)
                : variants(variants), variantsName(variantsName), nameBFMap(nameBFMap), tokenNameBFMap(tokenNameBFMap) {}

        string generateSoundness();
    };
}

#endif //ARTIFACT_SOUNDNESS_PRINTER_HH
