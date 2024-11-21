# include <stdlib.h>

// Call back function which operates on the the number
int operate_on_num(int n);

struct Counter {
    int num;
};

struct Counter* create(){
    struct Counter* c = (struct Counter*)malloc(sizeof(struct Counter));
    c->num = 0;
    return c;
}

struct Counter* add_one(struct Counter* c){
    c->num += 1;
    return c;
}

struct Counter* get_num(struct Counter* c){
    operate_on_num(c->num);
    return c;
}