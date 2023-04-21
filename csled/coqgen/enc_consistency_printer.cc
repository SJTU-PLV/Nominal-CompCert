//
//
//

#include "enc_consistency_printer.hh"
#include "encoder.hh"
#include "decoder.hh"
#include "../ir/ir.hh"
#include "coqgen.hh"
#include <string>
#include <vector>
#include <algorithm>
#include <sstream>
#include <map>
#include <cassert>
#include <utility>

#define SLICE 48

using namespace std;
using namespace coq;

static bool FAST_NO_CONFORM=true;
static bool FAST_NO_ORTH=true;

namespace ltac {
static string solve_try_skip_n = "solve_try_skip_n";
static string solve_try_first_n = "solve_try_first_n";
static string solve_equal = "solve_equal";
static string solve_assertion = "solve_assertion";
static string get_len_facts = "get_len_facts";
static string destruct_builtIn = "destruct_builtIn";
static string solve_preserve = "solve_preserve_klass";
static string solve_utype = "solve_klass";
static string simpl_branch_encode = "simpl_branch_encode";
static string simpl_branch_encode_instr ="simpl_branch_encode_instr";
static string save = string("save") + to_string(SLICE);
static string destruct_neq_list = "destruct_neq_list";
static string destruct_uncare_bit = "destruct_uncare_bit";
static string solve_klass_ret_nil="solve_klass_ret_nil";
static string rewrite_const_byte_in_goal="rewrite_const_byte_in_goal";
static string simpl_klass_encode = "simpl_klass_encode";
static string simpl_imm_encode="simpl_imm_encode";//may useless
}

static string fetch_EQ_n(int &cnt){
    static string EQ[3]={"EQ","EQ1","EQ0"};//monadinv result's names
    string EQ_n;
    if(cnt>2){EQ_n="EQ"+to_string(cnt-1);cnt++;}
    else EQ_n=EQ[cnt++];
    return EQ_n;
}

string Consistent_Proof_For_Single_Definition(string varName,ir::Definition *definition) {
    int lengthfactCnt = 0;
    stringstream len_fact;
    stringstream solve_ltac;
    int EQcnt=0;
    for (auto conj:definition->getConstraints().getConstraints()) {
        //the length of this semi
        int localLength = 0;

        // no parameters and utypes, must be constant
        if (conj->getPConstraints().empty() && conj->getUtConstraints().empty()) {
            solve_ltac << ltac::solve_try_skip_n << "." << endl;
            continue;
        }
        if (!conj->getPConstraints().empty()) {
            //calculate bytes length
            auto token = conj->getPConstraints()[0]->getToConstrain()->getToken();
            localLength = token->getTokenWidth();
            
            if (conj->getUtConstraints().empty()){
                // xxx;reg_op = 3;xxx
                if (conj->getPConstraints()[0]->getToConstrain()->isSubField()) {
                    solve_ltac << ltac::solve_try_first_n << "." << endl;
                    for (auto pCons:conj->getPConstraints()) {
                            solve_ltac << ltac::solve_assertion << "." << endl;
                    }
                }
                //...;imm32;...
                else {
                    fetch_EQ_n(EQcnt);//only add the cnt
                    ++lengthfactCnt;
                    assert(conj->getPConstraints().size() == 1);
                    solve_ltac << ltac::solve_try_first_n << "." << endl
                            << ltac::solve_assertion << "." << endl;
                }
            }
            //xx;reg_op = 3 & Eaddr;xx
            else {
                string EQ=fetch_EQ_n(EQcnt);
                assert(conj->getUtConstraints().size()==1);
                auto utype_name = conj->getUtConstraints()[0]->getParam()->getUType()->getTypeName();
                string Enc="encode_"+utype_name;
                string Preserve=Enc+"_preserve";
                solve_ltac << ltac::simpl_klass_encode+" "+EQ<< "." <<endl
                           << ltac::solve_preserve << " "+Enc+" "+Preserve << "." <<endl;
                
                // We only handle the case that the length of the common prefix is 8 
                if (localLength == 8) {
                    //prove Ptype
                    solve_ltac << ltac::solve_try_first_n << "." << endl;
                    for (auto pCons:conj->getPConstraints()) {
                            solve_ltac << ltac::solve_assertion << "." << endl;
                    }
                    auto utype_name = conj->getUtConstraints()[0]->getParam()->getUType()->getTypeName();
                    //solve_klass Enc(encoder function)
                    string Enc="encode_"+utype_name;
                    string Consistency=Enc+"_consistency";
                    solve_ltac << ltac::solve_utype <<" "+Enc+" "+Consistency<< "." << endl;
                }
                else {assert(false);}
            }
        }
        else if (!conj->getUtConstraints().empty()) {
            assert(conj->getUtConstraints().size() == 1);
            auto utype_name = conj->getUtConstraints()[0]->getParam()->getUType()->getTypeName();
            string Enc="encode_"+utype_name;
            string Consistency=Enc+"_consistency";
            solve_ltac << ltac::solve_utype <<" "+Enc+" "+Consistency<< "." << endl;
        }
        solve_ltac << ltac::solve_try_skip_n << "." << endl;
    }
    // len_fact << "do " << to_string(lengthfactCnt) + " " << ltac::get_len_facts << "." << endl; 
    solve_ltac << ltac::solve_equal << "." << endl;
    stringstream retValueStream;
    
    string ret = solve_ltac.str();
    return ret;
}

string generateConsistentProof(const string &varName, const pair<string, ir::Definition *> &nameDef, bool moreParam, const string& params, int cnt, int def_num) {
    //general part
    stringstream proof;
    // proof<<"idtac \"========== Start to prove Encode "+varName+" Consistency ==========\"."<<endl;
    string wildcards; // default length is 8
    if(moreParam)wildcards="_ _ _ _ _ _ _ _";

    proof << "intros " << params << " HEncode." << endl;

    //if (def_num >= SLICE) proof<< ltac::save + "." << endl;
    proof << "repeat ind_builtIn;" << endl // destruct all builtin data
          << "generalize (" + varName + "_conform _ " + wildcards + " l _ HEncode);intros HBpT;simpl in HBpT." << endl;

    string simpl_branch=moreParam?ltac::simpl_branch_encode:ltac::simpl_branch_encode_instr;

    proof << "(*prove " + nameDef.first + "*)" << endl;
    proof<<"idtac \"Encode Consistency: "+ nameDef.first + " "+ to_string(cnt+1)+"/"+to_string(def_num)+"\"."<<endl;

    proof << "unfold decode_" + varName + "." << endl;
    // simpl branch
    // proof << "unfold decode_" + varName + "." << endl;
        //<< "repeat simpl_branch_" + varName + ";" <<endl;        
    //e.g simpl_branch_instruction_opt instruction_bp_in_list0 instruction_bp_neq01.

    //simpl_branch_encode HIN BPfact Enc(encoder) Otrh(orth lemma) 
    //if moreParam there is different ltac
    int save_time = 0;
    for (int k=0;k<cnt;++k){
        string list_fact = varName + "_bp_in_list" + to_string(k);
        string neq_fact = varName + "_bp_neq" + to_string(k) + "_" + to_string(cnt);
        string Enc="encode_"+varName;
        string Orth=nameDef.first+"_orth";
        proof << simpl_branch<<" "<<list_fact << " "   
              << neq_fact << " " << Enc << " "<<Orth<<"."<<endl;
        
        // unfold Hsave
        // if(save_time < (k+1)/SLICE) {
        //     string Hsave = "Hsave" + to_string(save_time);
        //     proof << "unfold " << Hsave << ";clear " << Hsave << "." << endl;
        //     ++save_time;
        // }
    }

    // last rewrite HTrue 
    //independent to moreParam
    proof << ltac::simpl_branch_encode << "_last." <<endl; 

    // destruct all list with fixed length
    proof << "repeat destr_all_lists." << endl;
    // monadInv HEncode, can be more faster
    proof << "try simpl in HEncode;repeat decision_inv;monadInv HEncode;" << endl;
    // normalize
    proof << "repeat rewrite<-app_comm_cons;repeat rewrite<-app_assoc." << endl;


    auto proofbody = Consistent_Proof_For_Single_Definition(varName,nameDef.second);
    proof << proofbody;
    
    return proof.str();
}

bool isFullyQualified(vector<pair<string, ir::Definition *>> &variants) {
        for (auto &nameDef:variants) {
            if (!nameDef.second->isFullyQualified()) {
                return false;
            }
        }
        return true;
}

// generate a consistency lemma for each instruciton
// and then compose them into a top level lemma
// in order to reduce the memory consumption
string EncConsistency::generateEncConsistency() {

    string ret;
    auto hasAdditionalParameter = !isFullyQualified(variants);
    int common_prefix_length=8;

    string prefix_list, prefix_bits;
    if(hasAdditionalParameter){
        prefix_list="[";
        
        for(int i=1;i<=common_prefix_length;++i){
            if(i==common_prefix_length)
                prefix_list+="b"+to_string(i);
            else
                prefix_list+="b"+to_string(i)+";";

            prefix_bits+="b"+to_string(i)+" ";
        }
        prefix_list+="]";
    }

    int cnt=0;
    int def_num=variants.size();

    for(auto &def:variants){
        //initialize
        Lemma lemmaDef;
        lemmaDef.name = "encode_" + def.first + "_consistency";
        stringstream body;

        string params_string;
        //parameter names
        for (auto param:def.second->getUTypeParams()) {
            params_string+=param->getParamName()+" ";
        }
        for (auto param:def.second->getBuiltInParams()) {
            params_string+=param->getParamName()+" ";
        }

        string forall_params=string("bin l")+" "+prefix_bits+" "+params_string;
        string kls=def.first + " " +  params_string;

        //FIXME: if some klass is fully-qualified? Does it work?
        //for simplicity, we use b1-b8 to represent the common prefix
        body << "forall "<<forall_params<<"," << endl
             << "encode_" + variantsName + " (" + kls + ") " + prefix_list + " = OK bin ->" << endl
             << "decode_" + variantsName + " (bin++l) = OK(" + kls + ", length(bin)).";
    
        lemmaDef.body = body.str();
        //generate proof
        lemmaDef.proof = generateConsistentProof(variantsName, def, hasAdditionalParameter, forall_params, cnt, def_num) + "Qed.\n";

        ++cnt;
        //lemmaDef.proof = "Admitted.";
        ret+=lemmaDef.toString()+"\n";
    }

    // top level theorem
    Lemma lemmaDef;
    lemmaDef.name = "encode_" + variantsName + "_consistency";
    stringstream body, proof;
    string forall_params=string("bin l")+" "+prefix_bits+" "+"k";
    body << "forall "<<forall_params<<"," << endl
             << "encode_" + variantsName + " k " + prefix_list + " = OK bin ->" << endl
             << "decode_" + variantsName + " (bin++l) = OK(k, length(bin)).";
    lemmaDef.body = body.str();
    proof << "intros. destruct k." << endl;

    for(auto &def:variants){
        proof << "eapply encode_" + def.first + "_consistency;eauto." <<endl;
    }
    lemmaDef.proof=proof.str() + "Qed.\n";
    ret+=lemmaDef.toString()+"\n";

    return ret;

}


//for case: ...;reg_op=3&Ev;...
//need Ev's preserve lemma for the conform
//similar to "destruct_longest_const_list"
static string extract_untouch_part(ir::SemiConstraint& semi){
    int EQcnt=0;
    stringstream proof;

    for(auto &conj:semi.getConstraints()){
        auto cCon=conj->getCConstraints();
        //...;reg_op=3;...
        //there is const part
        if(cCon.size()!=0){
            if(cCon[0]->getLength()<=8){
                //...;Ev&reg_op=3;...
                if(conj->getUtConstraints().size()==1){
                    string name=conj->getUtConstraints()[0]->getParam()->getParamName();
                    string EQ=fetch_EQ_n(EQcnt);
                    string Enc="encode_"+name;
                    string Preserve=Enc+"_preserve";
                    string simpl=ltac::simpl_klass_encode+" "+EQ;
                    string solve_preserve=ltac::solve_preserve+" "+Enc+" "+Preserve;
                    proof<<simpl+";\n"+solve_preserve+";"<<endl;
                    break;
                }
            }
            // else {
            //     string EQ=fetch_EQ_n(EQcnt);
            //     string simpl=ltac::simpl_imm_encode+" "+EQ;
            //     proof<<simpl<<";"<<endl;
            // }
        }
    }
    return proof.str();
}

//l b l' k
//l l' k
string EncConsistency::generateConform(){
    Lemma lemmaDef;
    lemmaDef.name=variantsName+"_conform";
    auto hasAdditionalParameter = !isFullyQualified(variants);
    stringstream body;
    int def_num=variants.size();
    // Since we assume that the common prefix of the u-type is one byte, 
    // and we do not have a function to compute the length of the common prefix
    // So we leave this for future work
    int common_prefix_length=8;
    if(hasAdditionalParameter){
        string prefix_list="[", prefix_bits;
        for(int i=1;i<=common_prefix_length;++i){
            if(i==common_prefix_length)
                prefix_list+="b"+to_string(i);
            else
                prefix_list+="b"+to_string(i)+";";

            prefix_bits+="b"+to_string(i)+" ";
        }
        prefix_list+="]";

        body<<"forall l "<<prefix_bits<<"l' k,"<<endl
            << "encode_" + variantsName + " k "<<prefix_list<<" = OK l ->" << endl
            <<variantsName+"_op_to_bp "+"("+variantsName+"_to_op k) (l++l')=true."<<endl;
    }
    else {
        body<<"forall l l' k,"<<endl
            << "encode_" + variantsName + " k = OK l ->\n" << endl
            <<variantsName+"_op_to_bp "+"("+variantsName+"_to_op k) (l++l')=true."<<endl;
    }
    lemmaDef.body=body.str();
    
    stringstream proof;    
    proof<<"idtac \"========== Start to prove Encode "+variantsName+" Conform ==========\"."<<endl;
    //proof only need to destruct the byte to bits and then apply "ring" tactic
    proof<<"intros until k."<<endl
         <<"induction k;simpl;"<<endl
         <<"intros Enc;monadInv Enc;"<<endl
         <<"repeat ind_builtIn;repeat destr_all_lists."<<endl<<endl; // we should destruct the builtins into bits

    int cnt=0;
    //generate for each branch
    for(auto &def:variants){
        proof<<"(*prove " + def.first + "_conform Lemma *)" << endl;
        proof<<"idtac \"Encode Conform: "+ def.first + " "+ to_string(cnt+1)+"/"+to_string(def_num)+"\"."<<endl;

        proof<<extract_untouch_part(def.second->getConstraints());

        //common part for each
        proof<<"autounfold with "+variantsName+"_bpdb;"<<endl //unfold xx_bp
         <<"autounfold with bitfields;"<<endl
         <<"cbn [proj1_sig] in *;"<<endl
         <<"cbn [app];"<<endl //for case ...;Ev;Iz;...
        //  <<"repeat rewrite bytes_to_bits_cons_correct by auto;"<<endl
         <<"(repeat "+ltac::destruct_neq_list+";ring)."<<endl<<endl;//if there is neq pattern

         ++cnt;
    }

    if(FAST_NO_CONFORM)lemmaDef.proof="Admitted.";
    else lemmaDef.proof=proof.str()+"\nQed.";
    // lemmaDef.proof="Admitted.";
    return lemmaDef.toString();
}



static string destruct_longest_const_list(ir::SemiConstraint& semi){
    int EQcnt=0;
    stringstream proof;
    //may be useless,solve it: opcode;imm32;fld %x
    //bool middle_imm=false;
    //int not_yet_destruct=0;

    for(auto &conj:semi.getConstraints()){
        auto cCon=conj->getCConstraints();
        //...;reg_op=3;...
        //there is const part
        if(cCon.size()!=0){
            //FIXME assume every const_constrain are in same token
            for(int i=0;i<cCon[0]->getLength()/8;++i){
                if(conj->getUtConstraints().size()==0){
                    proof<<"destruct l as [|ii l];cbn [app] in *;"<<endl
                         <<"[repeat decision_inv;monadInv Enc|destr_byte ii]."<<endl;
                }
                //...;Ev&reg_op=3;...
                else{
                    assert(conj->getUtConstraints().size()==1);
                    string name=conj->getUtConstraints()[0]->getParam()->getParamName();
                    string Len="encode_"+name+"_len";
                    string EQ=fetch_EQ_n(EQcnt);
                    string solve=ltac::solve_klass_ret_nil+" "+EQ+" "+Len;
                    proof<<"destruct l as [|ii l];cbn [app] in *;"<<endl
                         <<"[repeat decision_inv;monadInv Enc;"+solve+"|destr_byte ii]."<<endl;
                    break;//is it right?
                }
            }
        }
        else if(conj->getUtConstraints().size()==0&&conj->getPConstraints().size()!=0){
            break;
            //FIXME: unable to solve -> opcode;imm32;const_part
        }
    }
    return proof.str();
}


string generateOrthProof(string varName, const pair<string, ir::Definition *> &def, bool moreParam){    
    //general part
    stringstream proof;
    // proof<<"idtac \"========== Start to prove Encode "+varName+" Orthogonal ==========\"."<<endl;

    proof<<"intro BpIn. intro Enc."<<endl;
    //get bp_true fact
    if(moreParam){
        string wildcards="_ _ _ _ _ _ _ _"; //assume common prefix is 8 bits length

        proof<<"generalize ("+varName+"_conform _ "+wildcards+" l' _ Enc)."<<endl;
    }
    else proof<<"generalize ("+varName+"_conform _ l' _ Enc)."<<endl;
    //Bp: bp_true
    proof<<"intro Bp."<<endl
         <<"intro Neq."<<endl
         <<"simpl in *;"<<endl
        //  <<"induction k;simpl in *;"<<endl
         <<"monadInv Enc;repeat ind_builtIn;repeat destr_all_lists;simpl in *."<<endl;

    proof<<extract_untouch_part(def.second->getConstraints());

    //destruct and simpl
    proof<<"repeat destruct BpIn as [BpIn| BpIn];subst;"<<endl
         // <<"repeat rewrite bytes_to_bits_cons_correct by auto;"<<endl
         <<"apply bpt_neq_sound in Neq;try contradiction;"<<endl
         <<"(autounfold with "+varName+"_bpdb);"<<endl
         <<"repeat "+ltac::destruct_neq_list+";"<<endl
         <<"repeat rewrite bp_and_eq;repeat rewrite bp_eq_eq;repeat rewrite bp_neq_eq;ring."<<endl; // rewrite the bp_and, bp_eq and bp_neq
    proof<<endl;

    return proof.str();

}


//bp l l' b k
// generate a orthogonal lemma for each branch
string EncConsistency::generateOrth(){
    string ret;
    auto hasAdditionalParameter = !isFullyQualified(variants);
    int common_prefix_length=8;

    string prefix_list, prefix_bits;
    if(hasAdditionalParameter){
        prefix_list="[";
        
        for(int i=1;i<=common_prefix_length;++i){
            if(i==common_prefix_length)
                prefix_list+="b"+to_string(i);
            else
                prefix_list+="b"+to_string(i)+";";

            prefix_bits+="b"+to_string(i)+" ";
        }
        prefix_list+="]";
    }

    int cnt=0;
    int def_num=variants.size();

    for(auto &def:variants){
        Lemma lemmaDef;
        lemmaDef.name=def.first+"_orth";
        stringstream body;
        string params_string;

        //parameter names
        for (auto param:def.second->getUTypeParams()) {
            params_string+=param->getParamName()+" ";
        }
        for (auto param:def.second->getBuiltInParams()) {
            params_string+=param->getParamName()+" ";
        }
        string forall_params=string("bp l l'")+" "+prefix_bits+params_string;
        body<<"forall "<<forall_params<<","<<endl
            <<"In bp "+variantsName+"_bp_list ->"<<endl
            <<"encode_"+variantsName+" ("<<def.first<<" "<<params_string<<") "<<prefix_list<<" = OK l ->"<<endl
            <<"bpt_neq "<<def.first<<"_bp bp ->"<<endl
            <<"bp (l++l') = false.";

        //use klass_bp_orth to prove it
        lemmaDef.body=body.str();
        // add introduction tactics
        lemmaDef.proof+="intros "+forall_params+".\n";
        lemmaDef.proof+="(*prove " + def.first + "_orth Lemma *)\n"+"idtac \"Encode Orthogonal: "+ def.first + " "+ to_string(cnt+1)+"/"+to_string(def_num)+"\".\n";

        if(FAST_NO_ORTH)lemmaDef.proof="Admitted.";
        else lemmaDef.proof+=generateOrthProof(variantsName,def,hasAdditionalParameter)+"\nQed.";
        //lemmaDef.proof="Admitted.";

        ret+=lemmaDef.toString()+"\n";
        ++cnt;
    }

    return ret;
}

//copy from dec_consistency_printer.cc
static void set_touch_bits(bool tb[],vector<pair<string,ir::Definition*>> &variants){
    for (auto &nameDef:variants){
        //first conjunction
        auto conj=nameDef.second->getConstraints().getConstraints()[0];
        for(auto &paraCon:conj->getPConstraints()){
            assert(paraCon->getToConstrain()->getWidth()<=8);
            int begin,end;
            begin=paraCon->getToConstrain()->getBegin();
            end=paraCon->getToConstrain()->getEnd();
            for(int i=end;i<=begin;++i)tb[i]=true;
        }
        for(auto &cCon:conj->getCConstraints()){
            assert(cCon->getToConstrain()->getWidth()<=8);
            int begin,end;
            begin=cCon->getToConstrain()->getBegin();
            end=cCon->getToConstrain()->getEnd();
            for(int i=end;i<=begin;++i)tb[i]=true;
        }
        assert(conj->getUtConstraints().size()==0);
    }
}

string EncConsistency::generatePreserve(){
    Lemma lemmaDef;
    lemmaDef.name="encode_"+variantsName+"_preserve";
    auto hasAdditionalParameter = !isFullyQualified(variants);
    //preserve only for untouch bits
    assert(hasAdditionalParameter&&!is_instruction);
    stringstream body;

    //common prefix is one
    bool touch_bits[8];
    set_touch_bits(touch_bits,variants);
    string inByte="";
    string exists="exists ";
    for(int i=1;i<=8;++i){
        if(!touch_bits[i-1]){
            inByte+="b"+to_string(i);
        }
        else {
            inByte+="b"+to_string(i)+"'";
            exists+="b"+to_string(i)+"' ";
        }
        if(i!=8)inByte+=";";
    }
    inByte="["+inByte+"]";
    exists+="l', ";
    string cp_byte="[b1;b2;b3;b4;b5;b6;b7;b8]";
    body<<"forall b1 b2 b3 b4 b5 b6 b7 b8 l k,"<<endl
        <<"encode_"+variantsName+" k "+cp_byte+" = OK l ->"<<endl;
    
    string conclusion="l = "+inByte+"++l'.";
    body<<exists<<conclusion;

    lemmaDef.body=body.str();

    stringstream proof;
    //adhoc:less test for this proof
    proof<<"intros until k."<<endl
         <<"induction k;simpl;intro Enc;"<<endl
         <<"repeat decision_inv;monadInv Enc;"<<endl
         <<"repeat ind_builtIn;repeat destr_all_lists;"<<endl //destruct all builtin
         <<"autounfold with bitfields;cbn[proj1_sig];"<<endl
         // <<"repeat rewrite bytes_to_bits_cons_correct by auto;"<<endl
         <<"simpl;repeat eexists."<<endl;
    
    lemmaDef.proof=proof.str()+"Qed.\n";

    return lemmaDef.toString();
}

//encode result length >=1 
string EncConsistency::generateEncLen(){
    assert(!is_instruction);
    Lemma lemmaDef;
    lemmaDef.name="encode_"+variantsName+"_len";

    stringstream body;
    body<<"forall b l k,"<<endl
        <<"encode_"+variantsName+" k b = OK l ->"<<endl
        <<"length l >=1."<<endl;

    lemmaDef.body=body.str();

    stringstream proof;
    proof<<"intros until k."<<endl
         <<"induction k;simpl;"<<endl
         <<"intro Enc;"<<endl
         <<"repeat decision_inv;monadInv Enc;simpl;lia."<<endl;
    
    lemmaDef.proof=proof.str()+"\nQed.\n";
    return lemmaDef.toString();
}

