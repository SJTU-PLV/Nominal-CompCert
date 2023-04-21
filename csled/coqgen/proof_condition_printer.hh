//
// Created by 徐翔哲 on 04/24/2021.
//

#ifndef ARTIFACT_PROOF_CONDITION_PRINTER_HH
#define ARTIFACT_PROOF_CONDITION_PRINTER_HH

#include <string>
#include <map>
#include <utility>
#include "../ir/ir.hh"

namespace coq {
    using namespace std;
    class ProofConditionPrinter {
        const map<string, ir::UType *> &irNameUTypeMap;
        stringstream sout;

    public:

        ProofConditionPrinter(const map<string, ir::UType *> &irNameUTypeMap) : irNameUTypeMap(irNameUTypeMap) {}

        string printProofCondition();

    };

}
#endif //ARTIFACT_PROOF_CONDITION_PRINTER_HH
