#ifndef BF_TRUE_HH
#define BF_TRUE_HH

#include <string>
#include <vector>
#include <algorithm>
#include <sstream>
#include <map>
#include "../ir/ir.hh"
#include <utility>


using namespace std;

namespace coq {
    class BFTrue {
        vector<pair<string, ir::Definition *>> &variants;
        //stringstream sout;//?
        string variantsName;
        bool is_instruction;
    public:
        BFTrue(const string &variantsName, vector<pair<string, ir::Definition *>> &variants,bool is_instr)
                : variants(variants), variantsName(variantsName),is_instruction(is_instr) {}

        string generateBptrue();
        string generateOrth();//useless
    };
}


#endif //BF_TRUE_HH