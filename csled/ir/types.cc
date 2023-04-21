//
// Created by 徐翔哲 on 12/03/2020.
//

#include "ir.hh"
#include "types.hh"
#include <algorithm>
#include<cassert>

//#define DEBUG

bool ir::UType::isFullyQualified() const {
    for (auto def:definitions) {
        if (!def->isFullyQualified()) {
            return false;
        }
    }
    return true;
}

string ir::UnsignedBits::toString() const {
    return "u" + to_string(width);
}


vector<const ast::Token*> _conjMaxPrefix(ir::ConjConstraint *constraint){
    vector<const ast::Token*> ret;

    if(!constraint->getUtConstraints().empty()){
        assert(constraint->getUtConstraints().size()==1);
        auto ucon = constraint->getUtConstraints()[0];
        auto ucon_max_prefix = ucon->getParam()->getUType()->getMaxPrefixTokens();
        ret.insert(ret.end(),ucon_max_prefix.begin(),ucon_max_prefix.end());
    }
    for(auto pcon:constraint->getPConstraints()){
        auto token = pcon->getToConstrain()->getToken();
        if(ret.empty()){
            ret.push_back(token);
        }
        else {
            bool exist = false;
            for(auto ret_token:ret)if(token->getTokenName() == ret_token->getTokenName()) exist = true;
            assert(exist);
        }
    }
    for(auto ccon:constraint->getCConstraints()){
        auto token = ccon->getToConstrain()->getToken();
        if(ret.empty()){
            ret.push_back(token);
        }
        else {
            bool exist = false;
            for(auto ret_token:ret)if(token->getTokenName() == ret_token->getTokenName()) exist = true;
            assert(exist);
        }
    }

#ifdef DEBUG
    for(auto token:ret)
        std::cout<<"_conjMaxPrefix "<<token->getTokenName()<<endl;
#endif
    return ret;
}

vector<const ast::Token*> _semiMaxPrefix(ir::SemiConstraint *constraint){
    vector<const ast::Token*> ret;
    for (auto conj:constraint->getConstraints()){
        auto conj_max = _conjMaxPrefix(conj);
        //assert no conincidence
        //contentate them
        bool no_coin = true;
        for (auto conj_token:conj_max){
            for (auto ret_token:ret){
                if (ret_token->getTokenName() == conj_token->getTokenName()) no_coin = false;
            }
        }    
        assert(no_coin);
        ret.insert(ret.end(),conj_max.begin(),conj_max.end());
    if(!conj->getUtConstraints().empty()) break;
    }
#ifdef DEBUG
    for(auto token:ret)
        std::cout<<"_semiMaxPrefix "<<token->getTokenName()<<endl;
#endif
    return ret;
   
}

vector<const ast::Token*>  ir::UType::getMaxPrefixTokens()const{
    vector<const ast::Token*> ret;
    for (auto def:definitions){
        auto tokens = _semiMaxPrefix(&def->getConstraints());
        if(ret.empty()){
            ret.insert(ret.end(),tokens.begin(),tokens.end());
        }
        else {
            vector<const ast::Token*> new_prefix;
            int max_prefix_len = 0;
            while(max_prefix_len<ret.size() && max_prefix_len<tokens.size()){
                if(!(ret[max_prefix_len]->getTokenName() == tokens[max_prefix_len]->getTokenName()))break;
                new_prefix.push_back(ret[max_prefix_len]);
                ++ max_prefix_len;
            }
            ret = new_prefix;
        }
    }
#ifdef DEBUG
    for(auto token:ret)
        std::cout<<"utype::getMaxPrefixTokens "<<token->getTokenName()<<endl;
#endif
    return ret;
}


//length=8*n, Eaddr:11000111
//only utype can generate
//not yet debug for nest utype
//unfinished
vector<bool>  ir::UType::getMaxMask()const{

    auto max_tokens = getMaxPrefixTokens();
    int len = 0;
    for(auto token:max_tokens){
        len+=token->getTokenWidth();
    }
    assert(len%8==0);
    auto ret = new vector<bool>(len,false);
    
    for(auto def:definitions){
        auto semic = def->getConstraints();
        int loc = 0;//ret start location
        int token_loc = 0;//which token
        for(auto conjc:semic.getConstraints()){
            if(token_loc>=max_tokens.size())break;

            int conj_len=0;
            for (auto ccon:conjc->getCConstraints()){
                //get_max_prefix fail
                assert(ccon->getToConstrain()->getToken()->getTokenName() == max_tokens[token_loc]->getTokenName());
                auto fld = ccon->getToConstrain();
                for(int i=fld->getBegin();i>=fld->getEnd();--i)ret->assign(i+loc,true);
            }

            for(auto pcon:conjc->getPConstraints()){
                //TODO
            }

        }
    }

}
