fn main() {
    
    let a : i32 = Box(12);
    loop {
        if t() {
            a = Box(13); 
        }
        else { 
            a = Box(3); 
            let b : i32 = a;
        }
    }

}

fn t() -> bool {
    return false;
}