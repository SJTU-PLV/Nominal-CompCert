//
// Created by 徐翔哲 on 12/03/2020.
//

#ifndef FRONTEND_TYPES_HH
#define FRONTEND_TYPES_HH

#include <string>
#include <vector>
#include "../parser/ast.hh"

using namespace std;
namespace ir {
    class Definition;

    class IRType {
    public:
        virtual bool isBuiltIn() {
            return false;
        }
    };

    class UType : public IRType {
    private:
        string typeName;
        vector<Definition *> definitions;
    public:
        UType(const string &typeName) : typeName(typeName) {}

        const string &getTypeName() const {
            return typeName;
        }

        void addDefinition(Definition *def) {
            definitions.push_back(def);
        }

        const vector<Definition *> &getDefinitions() const {
            return definitions;
        }

        bool isFixLength() const{
            //FIXME we assume all the UType is not fix length
            return false;
        }

        int getLength() const{
            return -1;
        }

        vector<bool> getMaxMask() const;
        vector<const ast::Token*> getMaxPrefixTokens()const;

        bool isFullyQualified()const;

    };

    class Instruction {
    private:
        string instrName;
        Definition *definition;
    public:
        Instruction(const string &instrName, Definition *definition)
                : instrName(instrName), definition(definition) {}

        const string &getInstrName() const {
            return instrName;
        }

        void setInstrName(const string &instrName) {
            Instruction::instrName = instrName;
        }

        Definition *getDefinition() const {
            return definition;
        }

        void setDefinition(Definition *definition) {
            Instruction::definition = definition;
        }
    };

    class UnsignedBits : public IRType {
    private:
        int width = 0;
    public:
        UnsignedBits(int width) : width(width) {}

        int getWidth() const {
            return width;
        }

        bool isBuiltIn() override {
            return true;
        }

        string toString() const;
    };

    class Constant : public IRType {
    private:
        int value;
    public:
        Constant(int value) : value(value) {}

        int getValue() const {
            return value;
        }
    };
}

#endif //FRONTEND_TYPES_HH
