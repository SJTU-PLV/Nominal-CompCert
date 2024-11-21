// ../../../ccomp counter.rs counter.c -o counter

// not support extern type for now
struct Counter {
    num: i32
}

extern fn create() -> Box<Counter>

extern fn add_one(c: Box<Counter>) -> Box<Counter>

extern fn get_num(c: Box<Counter>) -> Box<Counter>

fn operate_on_num(n: i32) -> i32{
    printf("The number in the counter is %d\n", n);
    return 0;
}

fn main(){
    let c : Box<Counter> = create();
    let n : i32 = 10;
    while (true) {
		if (0 < n) {
            c = add_one(c);
			n = n - 1;
			continue;
		}
		else {
			break;
		}
	};
    c = get_num(c);
}