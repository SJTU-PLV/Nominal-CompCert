//
// Created by 徐翔哲 on 12/29/2020.
//

#ifndef FRONTEND_UTIL_HH
#define FRONTEND_UTIL_HH

#include <string>


using namespace std;

namespace util {
    string _valueToBits(int value, int width);


    string _valueToHex(int value);

    inline string proj1(const string &builtInParamName) {
        return "(proj1_sig " + builtInParamName + ")";
    }
}


#endif //FRONTEND_UTIL_HH
