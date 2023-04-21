//
// Created by 徐翔哲 on 04/19/2021.
//

#ifndef ARTIFACT_TYPEPRINTER_HH
#define ARTIFACT_TYPEPRINTER_HH
#include <string>
#include <iostream>
#include <vector>
#include <map>
#include <fstream>
#include "../ir/ir.hh"
#include <utility>

namespace coq {
    class TypePrinter {
            vector<pair<string, ir::Definition *>> &variants;
            stringstream sout;
            string variantsName;
        public:
            TypePrinter(const string &variantsName, vector<pair<string, ir::Definition *>> &variants)
                    : variants(variants), variantsName(variantsName) {}

            string generateType();
    };
}


#endif //ARTIFACT_TYPEPRINTER_HH
