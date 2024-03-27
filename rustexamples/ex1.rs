
fn main() {
   let a: Box<i32> = Box(1)  {
       let b: Box<i32> = a {
           return b
       }
   }
}
