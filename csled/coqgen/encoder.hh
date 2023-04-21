//
// Created by 徐翔哲 on 12/27/2020.
//

#ifndef FRONTEND_ENCODER_HH
#define FRONTEND_ENCODER_HH

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
    //bool _isFullyQualified(map<string, ir::Definition *> &variants);

    class Encoder {
        vector<pair<string, ir::Definition *>> &variants;
        stringstream sout;
        string variantsName;
    public:
        Encoder(const string &variantsName, vector<pair<string, ir::Definition *>> &variants)
                : variants(variants), variantsName(variantsName) {}

        string generateEncoder();
    };
}


#endif //FRONTEND_ENCODER_HH
