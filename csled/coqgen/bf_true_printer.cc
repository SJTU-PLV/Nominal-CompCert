#include"bf_true_printer.hh"
#include"cassert"
#include"coqgen.hh"
#include <utility>

using namespace coq;

static bool FAST_NO_BP_TRUE=false;
static bool FAST_NO_ORTH=false;
namespace ltac {
    static string solve_klass_ret_nil="solve_klass_ret_nil";
    static string destruct_neq_list = "destruct_neq_list";
    static string destruct_uncare_bit = "destruct_uncare_bit";
}


static string fetch_EQ_n(int &cnt){
    static string EQ[3]={"EQ","EQ1","EQ0"};//monadinv result's names
    string EQ_n;
    if(cnt>2){EQ_n="EQ"+to_string(cnt-1);cnt++;}
    else EQ_n=EQ[cnt++];
    return EQ_n;
}

string bp_true_proof(string name,vector<int> &pattern){
    stringstream proof;
    proof<<"unfold "<<name<<"_bp."<<endl
         <<"intros until l."<<endl
        //  <<"repeat rewrite bytes_to_bits_cons_correct by auto."<<endl
         <<"intro Bp."<<endl;
    string true_str="[|ring_simplify in Bp;congruence];";
    string false_str="[ring_simplify in Bp;congruence|];";
    string destruct_bn="destruct b";
    int size=pattern.size();
    int bracket_num=0;
    //1:EQ true 2:EQ false 3:NEQ
    for(int i=1;i<=size;++i){
        if(pattern[i-1]==1){
            proof<<destruct_bn+to_string(i)+";"+true_str<<endl;
        }
        else if(pattern[i-1]==2){
            proof<<destruct_bn+to_string(i)+";"+false_str<<endl;
        }
        else if(pattern[i-1]==3){
            proof<<destruct_bn+to_string(i)+";("<<endl;
            bracket_num++;
        }
    }
    proof<<"repeat split;simpl in Bp;try congruence";
    for(int i=0;i<bracket_num;++i)proof<<")";
    proof<<".";
    return proof.str();
}

// internal[i]={low,high,EQ+NE,val}
vector<vector<int>> bp_interval(ir::SemiConstraint& semi,int &const_len){
    vector<vector<int>>ret;
    for(auto &conj:semi.getConstraints()){
        auto cCon=conj->getCConstraints();
        if(cCon.size()){
            //FIXME assume every const_constrain are in same token
            int cur_token_len=cCon[0]->getLength();
            for(auto &c:cCon){
                vector<int> interval(4,-1);
                interval[2]=c->getRelation();
                // +1 to match b_i
                interval[0]=8*const_len+c->getToConstrain()->getEnd()+1;
                interval[1]=8*const_len+c->getToConstrain()->getBegin()+1;
                interval[3]=c->getValue()->getValue();
                ret.emplace_back(interval);
            }
            if(cur_token_len<=8){
                const_len++;
            }
            else const_len+=cur_token_len/8;
        }
        if(conj->getUtConstraints().size()!=0)break;
    }
    return ret;
}


string BFTrue::generateBptrue(){
    stringstream all_bp_true_lemma;
    int def_num = variants.size();
    int cnt=0;
    for(auto &def:variants){
        string name=def.first;
        Lemma bptrue;
        bptrue.name=name+"_bp_true";

        string forall_part="forall ";
        string code_part="[";
        int blen=0;
        auto interval=bp_interval(def.second->getConstraints(),blen);
        assert(blen);
        blen*=8;
        for(int i=1;i<=blen;++i){
            // if(i-1&&(i-1)%8==0)bB_part+="::bB[[";
            forall_part+="b"+to_string(i)+" ";
            code_part+="b"+to_string(i);
            if(i!=blen)code_part+=";";
            else code_part+="]";
            // if(i%8==0)bB_part+="]]";
            // else bB_part+=";";
        }
        forall_part+="l,\n";
        code_part+="++l";
        string premise=name+"_bp "+"("+code_part+")"+"=true->\n";

        string conclusion="";
        //used for bp_true_proof generation
        ////1:EQ true 2:EQ false 3:NEQ
        vector<int> pattern(blen);
        for(int i=0;i<interval.size();++i){
            if(i)conclusion+="/\\";
            if(interval[i][2]==ir::EQ){
                int dec_val=interval[i][3];
                for(int idx=interval[i][0];idx<=interval[i][1];++idx){
                    if(dec_val%2){
                        conclusion+="b"+to_string(idx)+"=true";
                        pattern[idx-1]=1;
                    }
                    else {
                        conclusion+="b"+to_string(idx)+"=false";
                        pattern[idx-1]=2;
                    }
                    if(idx!=interval[i][1])conclusion+="/\\";
                    dec_val>>=1;
                }
            }
            else if(interval[i][2]==ir::NE){
                int dec_val=interval[i][3];
                string bits="[";
                for(int idx=interval[i][0];idx<=interval[i][1];++idx){
                    if(idx==interval[i][0])bits+="b"+to_string(idx);
                    else bits+=";b"+to_string(idx);
                    pattern[idx-1]=3;
                }
                bits+="]";
                string pat="[";
                for(int idx=interval[i][0];idx<=interval[i][1];++idx){
                    if(dec_val%2)pat="true"+pat;
                    else pat="false"+pat;
                    if(idx!=interval[i][1])pat=pat+";";
                    dec_val>>=1;
                }
                pat=pat+"]";

                conclusion+=bits+"<>"+pat;
            }
        }
        bptrue.body=forall_part+premise+conclusion+".";
        bptrue.proof="idtac \""+def.first+"_bp_true Lemma " + to_string(cnt+1)+"/"+to_string(def_num)+"\".\n";

        bptrue.proof+=bp_true_proof(def.first,pattern)+"\nQed.";

        all_bp_true_lemma<<bptrue.toString()<<endl<<endl;
        ++cnt;
    }
    return all_bp_true_lemma.str();
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
                proof<<"destruct l as [|ii l];cbn [app] in *;"<<endl
                    <<"[unfold addr_b_disp_bp in *;ring_simplify in Bp;congruence|destr_byte ii]."<<endl;
            }
        }
        else if(conj->getUtConstraints().size()==0&&conj->getPConstraints().size()!=0){
            break;
            //FIXME: unable to solve -> opcode;imm32;const_part
        }
    }
    return proof.str();
}


string generateOrthProof(string varName, vector<pair<string, ir::Definition *>> &variants){
    stringstream proof;
    proof<<"idtac \""+ varName +"_bp_orth Lemma\"."<<endl;
    proof<<"intros until l."<<endl
         <<"simpl."<<endl
         <<"intros BpIn1 BpIn2 Bp Neq."<<endl;
    
    //destruct bpin1, generate n goal
    proof<<"repeat destruct BpIn1 as [BpIn1| BpIn1];subst;try contradiction."<<endl<<endl;

    for(auto &def:variants){
        proof<<"(*prove " + def.first + "_bp_orth*)" << endl;
        proof<<"idtac \""+ def.first +"_bp_orth\"."<<endl;

        proof<<destruct_longest_const_list(def.second->getConstraints())<<endl;

        //apply bf_true lemma
        proof<<"apply "+def.first+"_bp_true in Bp.\ndestruct_conjunction Bp.\n";

        //destruct and simpl
        proof<<"repeat destruct BpIn2 as [BpIn2| BpIn2];subst;"<<endl
             <<"repeat rewrite bytes_to_bits_cons_correct by auto;"<<endl
             <<"apply bpt_neq_sound in Neq;try contradiction;"<<endl
             <<"(autounfold with "+varName+"_bpdb;try ring);"<<endl
             <<"(repeat "+ltac::destruct_neq_list+";simpl;"+ltac::destruct_uncare_bit+";ring)."<<endl;
        proof<<endl;
    }
    return proof.str();
}



// Unused
//e.g. different from the orth in EncConsistency.v
// Lemma Addrmode_bp_orth:
//   forall bp1 bp2 l,
//     In bp1 Addrmode_bp_list ->
//     In bp2 Addrmode_bp_list ->
//     bp1 l = true ->
//     bpt_neq bp1 bp2 ->
//     bp2 l =false.
string BFTrue::generateOrth(){
    Lemma lemmaDef;
    lemmaDef.name=variantsName+"_bp_orth"; 
    stringstream body;
    string bplist=variantsName+"_bp_list";
    body<<"forall bp1 bp2 l,"<<endl
        <<"In bp1 "+bplist+" ->"<<endl
        <<"In bp2 "+bplist+" ->"<<endl
        <<"bp1 (bytes_to_bits l) = true ->"<<endl
        <<"bpt_neq bp1 bp2 ->"<<endl
        <<"bp2 (bytes_to_bits l) = false."<<endl;

    lemmaDef.body=body.str();


    lemmaDef.proof=generateOrthProof(variantsName,variants)+"\nQed.";

    return lemmaDef.toString();
}