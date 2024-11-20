# Test cases for the Rust compiler 

This directory stores the test cases used to test the compiler.

## Tests

`factorial.rs`: it calculates the factorial of a given number

`fib.rs`: it calculates the fibonacci number

`list1.rs`, `list2.rs`, `list3.rs` and `list4.rs`: they implement the list data structure in different ways.

`elaborate_drop.rs`: a test case comes from the Rust RFC-0320 (https://rust-lang.github.io/rfcs/0320-nonzeroing-dynamic-drop.html)

`nested_box.rs`: a test case used to test partial move and its effect on drop elaboration
