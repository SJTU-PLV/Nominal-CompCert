#include "parser/ast.hh"
#include "parser/print_visitor.hh"
#include "syntax.tab.hh"
#include "ir/name_checker.hh"
#include <FlexLexer.h>
#include "ir/ir.hh"
#include "coqgen/coqgen.hh"
//#include "printer/coq.hh"
#include <fstream>
// #include "z3++.h"

//#include "foo.hh"

extern FILE *yyin;
extern ast::Specification *root;


int main(int argc, char **argv) {
    if (argc < 1) {
        cerr << "Specify the ssled file name!";
        exit(-1);
    }
    cout << "Hello SSLED" << endl;
    yyin = fopen(argv[1], "r");
//    yyin = fopen("sample.ssled", "r");
    yy::parser p;
    if (p.parse() == 0) {
        cout << "Syntax correct!" << endl;
//        ast::PrintVisitor visitor;
//        root->accept(visitor);
        cout << "Now check name references" << endl;
        preprocessor::NameChecker nameChecker;
        bool correct = nameChecker.check(root);
        cout << "Name checking result " << (correct ? "correct" : "wrong") << endl;
        ir::IRGenerator irGenerator(nameChecker.getNameTokenMap(),
                                    nameChecker.getNameFieldMap(),
                                    nameChecker.getNameKlassMap(),
                                    root);
        irGenerator.generate();

        coq::CoqPrinter printer(irGenerator.getNameBfMap(), irGenerator.getIrNameUTypeMap(),
                                irGenerator.getIrNameInstrMap());
        string filename = string("generated/EncDecRet.v"); //change file name
        fstream os(filename, fstream::out);
        cout << "===========COQ CODE WRITTEN IN " + filename + " =============" << endl;
        os << printer.print();
        os.flush();

        //BF true lemma
        string bf_true = string("generated/BFtrue.v"); // change file name
        fstream bf_os(bf_true, fstream::out);
        cout << "===========COQ BF=true PROOF CODE WRITTEN IN " + bf_true + " =============" << endl;
        bf_os << printer.bf_true_print();
        bf_os.flush();

        //Encode Consistency
        string filename_enc_consistency = string("generated/EncConsistency.v"); // change file name
        fstream enc_os(filename_enc_consistency, fstream::out);
        cout << "===========COQ Enc_Consistency PROOF CODE WRITTEN IN " + filename_enc_consistency + " ============="
             << endl;
        enc_os << printer.enc_consistency_print();
        enc_os.flush();

        //Decode Consistency
        string filename_dec_consistency = string("generated/DecConsistency.v");
        fstream dec_os(filename_dec_consistency, fstream::out);
        cout << "===========COQ Dec_Consistency PROOF CODE WRITTEN IN " + filename_dec_consistency + " ============="
             << endl;
        dec_os << printer.dec_consistency_print();
        dec_os.flush();

    } else {
        cout << "Syntax Error!" << endl;
    }

} 