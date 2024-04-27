fn main() {
    
    let mut a = Box::new(12);
    loop {
        if t() {
            // if (flag) drop(a)
            a = Box::new(13); 
        }
        else { 
            a = Box::new(3); 
            let b = a;
        }
    }

}

fn t() -> bool {
    return false;
}