//
// Created by 徐翔哲 on 12/30/2020.
//
#include "util.hh"
#include <string>
#include <iostream>
#include <map>
#include <vector>
#include <sstream>

using namespace std;
namespace util{

    string _valueToBits(int value, int width) {
        stringstream ret;
        ret << "[";
        vector<bool> bits;
        for (int i = 0; i < width; i++) {
            bits.push_back((value & 0x1) == 1);
            value >>= 1;
        }

        for (auto current = bits.begin(); current != bits.end(); current++) {
            bool b = *current;
            if(current==bits.begin())ret << (b ? "true" : "false");
            else ret << (b ? ";true" : ";false");
        }
        ret << "]";
        return ret.str();
    }

    static char digits[] = "0123456789ABCDEF";

    string _valueToHex(int value) {
        value &= 0xFF;
        char c[3];
        c[1] = digits[value & 0xF];
        value >>= 4;
        c[0] = digits[value];
        c[2] = 0;
        return c;
    }

}
