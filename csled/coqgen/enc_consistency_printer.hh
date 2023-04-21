//
//
//

#ifndef FRONTEND_CONSISTENCE_HH
#define FRONTEND_CONSISTENCE_HH

#include <string>
#include <vector>
#include <algorithm>
#include <sstream>
#include <map>
#include "../ir/ir.hh"
#include <utility>


using namespace std;

namespace coq {
    class EncConsistency {
        vector<pair<string, ir::Definition *>> &variants;
        //stringstream sout;//?
        string variantsName;
        bool is_instruction;
    public:
        EncConsistency(const string &variantsName, vector<pair<string, ir::Definition *>> &variants,bool is_instr)
                : variants(variants), variantsName(variantsName),is_instruction(is_instr) {}

        string generatePreserve();
        string generateOrth();
        string generateConform();
        string generateEncConsistency();
        string generateEncLen();
    };
}


#endif //FRONTEND_CONSISTENCE_HH
