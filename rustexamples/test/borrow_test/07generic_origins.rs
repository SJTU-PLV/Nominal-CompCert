fn main() {
	let reference_to_nothing : &i32 = dangle();
}

fn dangle() -> &i32 {
    let a : i32 = 2;
    return &a;
}
	
