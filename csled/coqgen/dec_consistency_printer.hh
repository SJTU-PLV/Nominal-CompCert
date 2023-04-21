// generation of decode consistency theorem

#ifndef DEC_CONSISTENCY_HH
#define DEC_CONSISTENCY_HH

#include <string>
#include <vector>
#include <algorithm>
#include <sstream>
#include <map>
#include "../ir/ir.hh"
#include <utility>

using namespace std;

namespace coq{
    class DecConsistency{
        vector<pair<string,ir::Definition*>> &variants;
        string variantsName;
        bool is_instruction;
    public:
        DecConsistency(const string &variantsName, vector<pair<string, ir::Definition *>> &variants,bool is_instr)
                : variants(variants), variantsName(variantsName),is_instruction(is_instr){}

        string generateConsistency();
        string generateGtLen();
    };

}



#endif