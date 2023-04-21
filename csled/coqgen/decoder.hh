//
// Created by 徐翔哲 on 12/30/2020.
//

#ifndef FRONTEND_DECODER_HH
#define FRONTEND_DECODER_HH

#include <string>
#include <vector>
#include <algorithm>
#include <sstream>
#include <map>
#include "../ir/ir.hh"
#include <utility>


using namespace std;

namespace coq {
    class Decoder {
        vector<pair<string, ir::Definition *>> &variants;
        stringstream sout;
        string variantsName;
    public:
        Decoder(const string &variantsName, vector<pair<string, ir::Definition *>> &variants)
                : variants(variants), variantsName(variantsName) {}

        string generateDecoder();
    };
}


#endif //FRONTEND_DECODER_HH
