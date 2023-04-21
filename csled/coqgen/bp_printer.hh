#ifndef BP_HH
#define BP_HH

#include "coqgen.hh"
#include <string>
#include <iostream>
#include <vector>
#include <fstream>
#include <cassert>


namespace coq {

    struct BitPattern {
        vector<bool> mask;
        vector<bool> pattern;
        ir::ConstraintRelation relation;

        BitPattern() = default;

        BitPattern(const BitPattern &other)
                : mask(other.mask), pattern(other.pattern), relation(other.relation) {}

        BitPattern &operator=(const BitPattern &other) {
            if (&other != this) {
                mask = other.mask;
                pattern = other.pattern;
                relation = other.relation;
            }
            return *this;
        }


        BitPattern operator|(const BitPattern &other) {
            BitPattern ret = *this;
            while (ret.mask.size() < other.mask.size()) {
                ret.mask.push_back(false);
                ret.pattern.push_back(false);
            }
            for (int i = 0; i < other.pattern.size(); i++) {
                if (other.mask[i] && ret.mask[i]) {
                    assert(other.pattern[i] == ret.pattern[i]);
                    ret.pattern[i] = other.pattern[i];
                }else if(other.mask[i]){
                    ret.pattern[i] = other.pattern[i];
                } else if (ret.mask[i]){
                    //do nothing
                }
                ret.mask[i] = other.mask[i] || ret.mask[i];
            }
            return ret;
        }

        string maskString()const{
            stringstream sout;
            for(auto b = mask.begin();b!=mask.end();b++){
                if(b==mask.begin())sout<<(*b ? "true" : "false");
                else sout<<(*b ? ";true" : ";false");
            }
            return sout.str();
        }

        string maskStringSMT()const{
            stringstream sout;
            for (const auto &b:mask) {
                sout << (b ? "1" : "0");
            }
            return sout.str();
        }

        string maskStringExtendedTo(const int width) const{
            stringstream sout;
            auto prefix = maskStringSMT();
            const int prefix_len = prefix.length();
            int toApp = width - prefix_len;
            assert(toApp>=0);
            string app(toApp, '0');
            sout << prefix << app;
            return sout.str();
        }

        string patternString()const{
            stringstream sout;
            for(auto b = pattern.begin();b!=pattern.end();b++){
                if(b==pattern.begin())sout<<(*b ? "true" : "false");
                else sout<<(*b ? ";true" : ";false");
            }
            return sout.str();
        }

        string patternStringSMT()const{
            stringstream sout;
            for (const auto &b:pattern) {
                sout << (b ? "1" : "0");
            }
            return sout.str();
        }

        string patternStringExtendedTo(const int width)const{
            stringstream sout;
            auto prefix = patternStringSMT();
            const int prefix_len = prefix.length();
            int toApp = width - prefix_len;
            assert(toApp>=0);
            string app(toApp, '0');
            sout << prefix << app;
            return sout.str();
        }
    };


    vector<BitPattern> *generateBitPattern(ir::Definition *definition);


}


#endif
