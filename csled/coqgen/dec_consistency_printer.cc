//generation of decode consistency theorem

#include"dec_consistency_printer.hh"
#include"cassert"
#include"coqgen.hh"
#include <utility>

#define SLICE 48

using namespace std;
using namespace coq;

static bool FAST_NO_LEN=false;
static bool SPEED_UP=true;//test the speeding ratio
namespace coq{
    namespace ltac{
        static string solve_try_skip_n = "solve_try_skip_n_decode ";
        static string solve_try_first_n = "solve_try_first_n_decode ";
        static string solve_try_get_n = "solve_try_get_n_decode ";
        static string simpl_branch = "simpl_branch_decode ";
        static string solve_builtin_dec ="solve_builtin_eq_dec_decode";
        static string destr_byte = "destr_byte ";
        static string destruct_conjunction = "destruct_conjunction";
        static string solve_utype = "solve_kls_decode ";
        static string destruct_const_byte_rewrite = "destruct_const_byte_rewrite ";
        static string solve_zero_len_list="solve_zero_len_list";
        static string save="save"+to_string(SLICE);
        static string rename_firstn_result = "rename_firstn_result ";
        static string destr_token = "destr_token ";
    }
}

//it would change the counter
static string fetch_EQ_n(int &cnt){
    static string EQ[3]={"EQ","EQ1","EQ0"};//monadinv result's names
    string EQ_n;
    if(cnt>2){EQ_n="EQ"+to_string(cnt-1);cnt++;}
    else EQ_n=EQ[cnt++];
    return EQ_n;
}


string Proof_For_Single_Def(const pair<string, ir::Definition*> &namedef,int common_token_num=1){

    auto definition=namedef.second;
    int EQ_cnt=0;
    int token_cnt=0;

    stringstream solve_ltac;
    for (auto conj:definition->getConstraints().getConstraints()) {
        ++token_cnt;
        //only const pattern
        //destruct hhex byte
        if (conj->getPConstraints().empty() && conj->getUtConstraints().empty()) {
            auto cCon=conj->getCConstraints();
            assert(cCon.size()>0);
            string EQ_n=fetch_EQ_n(EQ_cnt);
            //destruct l, use Decode_Len to congruence

            //solve skipn 
            solve_ltac << ltac::solve_try_skip_n << EQ_n+"." << endl;

            //rewrite Byte.repr xx
            // if(cCon.size()==1){
            //     int val=cCon[0]->getValue()->getValue();
            //     while(val!=0){
            //         solve_ltac<<ltac::destruct_const_byte_rewrite<<to_string(val%256)+"%Z."<<endl;
            //         val=(val>>8);
            //     }
            // }
            continue;
        }

        //has param pattern
        if(!conj->getPConstraints().empty()) {
            auto token = conj->getPConstraints()[0]->getToConstrain()->getToken();
            int localLength = token->getTokenWidth();
            
                // xxx;fld n & const_part;xxx
                if (conj->getUtConstraints().empty()){
                    if (conj->getPConstraints()[0]->getToConstrain()->isSubField()) {
                        string EQ_n=fetch_EQ_n(EQ_cnt);

                        // if not in common prefix, destruct the bits
                        if(token_cnt>common_token_num){
                            // we need to destruct the token into bits. Thus the read functions can be simplified
                            // the new name is "firstn_result"
                            solve_ltac << ltac::rename_firstn_result << EQ_n+"." << endl
                                    << ltac::solve_try_first_n << EQ_n+" Decode_Len."<< endl
                                    << ltac::destr_token << "firstn_result." << endl;
                        }
                        else{
                            solve_ltac << ltac::solve_try_first_n << EQ_n+" Decode_Len."<< endl;
                        }   

                    } 
                    // imm32 etc
                    else {
                        string EQ_n=fetch_EQ_n(EQ_cnt);
                        assert(conj->getPConstraints().size() == 1);
                        solve_ltac << ltac::solve_try_first_n << EQ_n+" Decode_Len." << endl;
                        //for encode bits_to_bytes
                        //solve_ltac<<"cbn [bind]."<<endl;
                    }
                }
                //...;reg_op=r&Ev;...
                //if there is const part? no need to destruct l !!
                else {
                    assert(conj->getUtConstraints().size()==1);
                    //common prefix=1
                    assert(localLength==8);
                    auto utype_name = conj->getUtConstraints()[0]->getParam()->getUType()->getTypeName();
  

                    string EQ_n_get=fetch_EQ_n(EQ_cnt);
                    string EQ_n_dec=fetch_EQ_n(EQ_cnt);
                    //need to destruct l and apply decode_utype_len lemma to contradict
                    //FIXME: unable to solve :Decode_Len: S..S(x1+x2..)=S..S (length l) unless lia is powerful..
                    //which is more than one klass
                    if(conj->getCConstraints().size()==0){
                        solve_ltac<<"destruct l as [|ii l];cbn [app] in *."<<endl
                                    //if l is []
                                  <<"apply decode_"+utype_name+"_len in "<<EQ_n_dec<<";simpl in Decode_Len;lia."<<endl
                                  <<"destr_byte ii."<<endl;
                    }
                    solve_ltac << ltac::solve_try_get_n << EQ_n_get+"." << endl;
                    //solve_kls_decode EQn Decode_Len consistency_theorem decode_function
                    //adhoc: Decode_Len
                    solve_ltac << ltac::solve_utype << EQ_n_dec << " Decode_Len "
                               << "decode_"+utype_name+"_consistency decode_"+utype_name+"."<< endl
                                //if utype is the last
                               <<"repeat "+ltac::solve_zero_len_list+"."<<endl;
                }
        }
        //only const pattern and klass pattern e.g. ...;reg_op=3&Ev;...
        else if (!conj->getUtConstraints().empty()) {
                assert(conj->getUtConstraints().size() == 1);
                string EQ_n=fetch_EQ_n(EQ_cnt);
                auto utype_name = conj->getUtConstraints()[0]->getParam()->getUType()->getTypeName();
                solve_ltac << ltac::solve_utype << EQ_n << " Decode_Len "
                               << "decode_"+utype_name+"_consistency decode_"+utype_name+"."<< endl
                                //if utype is the last
                               <<"repeat "+ltac::solve_zero_len_list+"."<<endl;
            }
        //skip the conj
        string EQ_n=fetch_EQ_n(EQ_cnt);
        solve_ltac << ltac::solve_try_skip_n << EQ_n+"." << endl;
    }

    //calculate b1 to bn, use bp_true lemma
    string bp_true=namedef.first+"_bp_true";
    solve_ltac<<"apply "+bp_true+" in Bp."<<endl
              <<ltac::destruct_conjunction+" Bp."<<endl;

    //if builtin_dec xxx then xxx
    // solve_ltac<<"repeat solve_builtin_eq_dec_decode."<<endl;
    solve_ltac << "autounfold with *. simpl." << endl;

    return solve_ltac.str();
}


//destruct l 
//simulate decoder
static string destruct_longest_const_list(string constr_name,ir::SemiConstraint& semi,bool is_instr){
    int EQ_cnt=0;
    stringstream proof;
    bool last=true;
    int common_prefix=1;
    for(auto &conj:semi.getConstraints()){
        if(!is_instr&&common_prefix){common_prefix--;continue;}
        //if no const part
        if(conj->getCConstraints().empty()){
            last=false;
            break;
        }
        //only const pattern
        if (conj->getPConstraints().empty() && conj->getUtConstraints().empty()) {
            string EQ_n=fetch_EQ_n(EQ_cnt);
            auto cCon=conj->getCConstraints();
            assert(cCon.size()>0);
            for(int i=0;i<cCon[0]->getLength()/8;++i){
                if(!is_instr){
                        proof<<"destruct l as [|ii l];cbn [app] in *."<<endl
                             <<"unfold "+constr_name+"_bp in Bp;simpl in Bp;congruence."<<endl;
                        proof<<ltac::destr_byte+"ii."<<endl;
                }
                else{
                    proof<<"destruct l as [|ii l];cbn [app] in *;"<<endl
                         <<"simpl in Decode_Len;"
                         <<"try injection Decode_Len as Decode_Len."<<endl
                         <<"congruence." <<endl;
                    proof<<ltac::destr_byte+"ii."<<endl;
                }
            }
            continue;
        }
        //has param pattern
        if(!conj->getPConstraints().empty()) {
            auto token = conj->getPConstraints()[0]->getToConstrain()->getToken();
            int localLength = (token->getTokenWidth() + 7) / 8;
            // xxx;R=1&fld 3;xxx 
            if (conj->getUtConstraints().empty()){
                //FIXME: unable to solve -> opcode;imm32;const_part
                //can use a lookahead method!!
                if(conj->getCConstraints().empty()){
                    //const_part not the end
                    last=false;
                    break;
                }
                string EQ_n_get=fetch_EQ_n(EQ_cnt);
                string EQ=fetch_EQ_n(EQ_cnt);
                if(!is_instr){
                        proof<<"destruct l as [|ii l];cbn [app] in *."<<endl
                             <<"unfold "+constr_name+"_bp in Bp;simpl in Bp;congruence."<<endl;
                        proof<<ltac::destr_byte+"ii."<<endl;
                }
                else{
                   proof<<"destruct l as [|ii l];cbn [app] in *;"<<endl
                         <<"simpl in Decode_Len;"
                         <<"try injection Decode_Len as Decode_Len."<<endl
                         <<"congruence." <<endl;
                    proof<<ltac::destr_byte+"ii."<<endl;
                }
            }
            //...;reg_op=r&const_part&Ev;...
            ////if there is const part? need to destruct l !!
            else{
                //break is right, because there is a klass
                if(conj->getCConstraints().empty()){
                    last=false;
                    break;
                }
                assert(is_instr);//FIXME
                assert(conj->getUtConstraints().size()==1);
                string utype_name=conj->getUtConstraints()[0]->getParam()->getParamName();
                string EQ_n_get=fetch_EQ_n(EQ_cnt);
                string EQ=fetch_EQ_n(EQ_cnt);
                proof<<"destruct l as [|ii l];cbn [app] in *;"<<endl
                     <<"simpl in Decode_Len;"
                     <<"try injection Decode_Len as Decode_Len."<<endl
                                //if l is []
                     <<"apply decode_"+utype_name+"_len in "<<EQ<<";simpl in Decode_Len;lia."<<endl;
                proof<<ltac::destr_byte+"ii."<<endl;
                last=false;
                break;
            }
        }
        //only const pattern and klass pattern e.g. ...;reg_op=3&Ev;...
        else if (!conj->getUtConstraints().empty()) {
            assert(conj->getUtConstraints().size() == 1);
            string EQ=fetch_EQ_n(EQ_cnt);
            auto utype_name = conj->getUtConstraints()[0]->getParam()->getUType()->getTypeName();
            proof<<"destruct l as [|ii l];cbn [app] in *;"<<endl
                 <<"simpl in Decode_Len;"
                 <<"try injection Decode_Len as Decode_Len."<<endl
                //if l is []
                 <<"apply decode_"+utype_name+"_len in "<<EQ<<";simpl in Decode_Len;lia."<<endl;
            proof<<ltac::destr_byte+"ii."<<endl;
            last=false;
            break;
        }
    }
    //other klass's consistency signature is different no need to destruct l
    if(last&&is_instr)proof<<"destruct l;[|simpl in Decode_Len;congruence]."<<endl;
    return proof.str();
}


string generateProof(const string varName, vector<pair<string, ir::Definition *>> &variants,bool is_instr){
    //common part
    stringstream proof;
    int def_num = variants.size();
    proof<<"idtac \"========== Start to prove Decode "+varName+" Consistency ==========\"."<<endl;
    //k is adhoc
    proof<<"intros until k. "<<endl
         <<"intro Dec. unfold decode_"+varName+" in Dec. "<<endl;
    // if(def_num>=SLICE)proof<<ltac::save+" Dec."<<endl; //saved name: Dec Hsave0 Hsave1 ...

    //first destruct bp and then induction k
    //proof<<"induction k;simpl."<<endl<<endl;
         
   
    
    int cnt=0;
    for(auto &def:variants){
        proof << "(*prove " + def.first + "*)" << endl;

        proof<<"idtac \"Decode Consistency: "+ def.first + " "+ to_string(cnt+1)+"/"+to_string(def_num)+"\"."<<endl;
        
        
        //destruct and find the branch
        //need to speed up
        //def.first = varName+cnt
        if(!SPEED_UP){
        string last_congruence="";
        if(def_num-cnt-1==0)last_congruence="congruence";
        else last_congruence="do "+to_string(def_num-cnt-1)+" "+ltac::simpl_branch+"Dec";
        proof<<"do "+to_string(cnt)+" "+ltac::simpl_branch+"Dec."<<endl
             <<"destruct "+def.first+"_bp eqn:Bp;[|"+last_congruence+"]."<<endl;
        }
        else {
            proof<<"try clear Bp."<<endl;//need to clear Bp!
            // if(cnt&&cnt%SLICE==0)proof<<"unfold Hsave"+to_string(cnt/SLICE-1)+" in Dec."<<endl;
            //destruct the bp, and induction k then try congruence
            proof<<"destruct "+def.first+"_bp eqn:Bp in Dec."<<endl
                 <<"monadInv_decode Dec."<<endl
                 <<"simpl. cbn [app] in *."<<endl;//simpl the encoder and simplify all the append operations
                // add Arguments builtin_eq_dec l l' : simpl never.
        }

        //monadinv
        // proof<<"autounfold with bitfields.\nrepeat destruct_const_byte_rewrite 0%Z.\ncbn [proj1_sig].\n";


        // proof<<destruct_longest_const_list(def.first,def.second->getConstraints(),moreParam)<<endl;
            
        //follow the encoder and decoder structure to generate
        if(is_instr) proof<<Proof_For_Single_Def(def,0); // common token number is zero
        else proof<<Proof_For_Single_Def(def);
        
        //simpl and finish
        proof<<"repeat eexists;simpl;auto;try lia."<<endl<<endl;

        ++cnt;
    }

    if(cnt&&cnt%SLICE==0)proof<<"unfold Hsave"+to_string(cnt/SLICE-1)+" in Dec."<<endl;
    proof<<"congruence."<<endl<<endl;
         
    return proof.str();

}


//FIXME
bool _isFullyQualified(vector<pair<string, ir::Definition *>> &variants) {
            for (auto &nameDef:variants) {
                if (!nameDef.second->isFullyQualified()) {
                    return false;
                }
            }
            return true;
        }

static void set_touch_bits(vector<bool> &tb,vector<pair<string,ir::Definition*>> &variants, int common_prefix_length){
    for (auto &nameDef:variants){
        //first conjunction
        auto conj=nameDef.second->getConstraints().getConstraints()[0];
        for(auto &paraCon:conj->getPConstraints()){
            assert(paraCon->getToConstrain()->getWidth()<=common_prefix_length);
            int begin,end;
            begin=paraCon->getToConstrain()->getBegin();
            end=paraCon->getToConstrain()->getEnd();
            for(int i=end;i<=begin;++i)tb[i]=true;
        }
        for(auto &cCon:conj->getCConstraints()){
            assert(cCon->getToConstrain()->getWidth()<=common_prefix_length);
            int begin,end;
            begin=cCon->getToConstrain()->getBegin();
            end=cCon->getToConstrain()->getEnd();
            for(int i=end;i<=begin;++i)tb[i]=true;
        }
        assert(conj->getUtConstraints().size()==0);
    }
}



string DecConsistency::generateConsistency(){

    Lemma lemmaDef;
    auto hasAdditionalParameter = !_isFullyQualified(variants);
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

    lemmaDef.name="decode_"+variantsName+"_consistency";
    stringstream body;

    // the prefix bits in the encoder
    string untouch_bits;
    if(hasAdditionalParameter){
        vector<bool> touch_bits(common_prefix_length,false);
        set_touch_bits(touch_bits,variants,common_prefix_length);
        for(int i=1;i<=common_prefix_length;++i){
            if(!touch_bits[i-1])untouch_bits+="b"+to_string(i);
            else untouch_bits+="false";
            if(i!=common_prefix_length)untouch_bits+=";";
        }
        untouch_bits="["+untouch_bits+"]";
    }


    string forall_params;
    string kls="k";

    if(is_instruction){
        forall_params=string("l l'")+" "+prefix_bits+" "+ kls;
        body << "forall "<<forall_params<<"," << endl;
        body << "decode_" + variantsName + " (l++l') = OK (" + kls +",length l) ->" <<endl;
        body << "encode_" + variantsName + " (" + kls + ") = OK l.";   
    }
    else {
        forall_params=string("l len")+" "+prefix_bits+" "+ kls;
        body << "forall "<<forall_params<<"," << endl;
        body << "decode_" + variantsName + " (" + prefix_list + "++l) = OK ("+ kls + ",len) ->" << endl;
        body << "exists l1 l2, l=l1++l2 /\\ len=8 + (length l1) /\\ encode_" + variantsName + " (" + kls + ") " + untouch_bits + " = OK (" + prefix_list + "++l1).";
    }

    lemmaDef.body=body.str();
    lemmaDef.proof=generateProof(variantsName, variants, is_instruction);
    // TODO: FIX
    lemmaDef.proof+="Admitted.";

    return lemmaDef.toString();

}


string DecConsistency::generateGtLen(){
    Lemma lemmaDef;
    lemmaDef.name="decode_"+variantsName+"_len";
    bool moreParam=!_isFullyQualified(variants);
    int def_num=variants.size();
    //assume common prefix is 1
    lemmaDef.body="forall l len k, decode_"+variantsName+" l=OK(k,len)->\nlen>=1.";

    stringstream proof;
    proof<<"idtac \"========== Start to prove Decode "+variantsName+" Gt Len ==========\"."<<endl;
    proof<<"intros until k.\ninduction k;\nintro Dec;\nunfold decode_"+variantsName+" in Dec.\n";

    //FIXME:assume no embeded klass

    int cnt=0;
    int size=variants.size();
    for(auto &def:variants){
        proof<<"idtac \"Decode Gt Len: "+ def.first + " "+ to_string(cnt+1)+"/"+to_string(def_num)+"\"."<<endl;
        string last_congruence="";
        if(size-cnt-1==0)last_congruence="congruence";
        else last_congruence="do "+to_string(size-cnt-1)+" "+ltac::simpl_branch+"Dec";
        proof<<"do "<<to_string(cnt)<<" simpl_branch_decode Dec."<<endl
            <<"destruct "+def.first+"_bp eqn:Bp;[|"+last_congruence+"]."<<endl
            <<"monadInv_decode Dec."<<endl
            <<"lia."<<endl<<endl;
        ++cnt;
    }
    lemmaDef.proof=proof.str()+"Qed.\n";
    

    return lemmaDef.toString();
}

