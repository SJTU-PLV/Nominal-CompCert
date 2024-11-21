# Test cases for the Rust compiler 

This directory stores the test cases used to test the compiler.

## Test cases

`factorial.rs`: it calculates the factorial of a given number

`fib.rs`: it calculates the fibonacci number

`list1.rs`, `list2.rs`, `list3.rs` and `list4.rs`: they implement the list data structure in different ways.

`elaborate_drop.rs`: a test case comes from the Rust RFC-0320 (https://rust-lang.github.io/rfcs/0320-nonzeroing-dynamic-drop.html)

`nested_box.rs`: a test case used to test partial move and its effect on drop elaboration

`counter`: it contains `counter.c` which implements a counter ADT in C and `main.rs` which invokes the method in C. It is an example of  separate compilation of safe Rust and unsafe code (C code).

## Run the test

In this directory, run `make` to compile all the test cases into executable code (suffix with `.rcompcert` which stands for Rust-Compcert), and then run `make test` to check the output of each test case.

```
make
make test
```

To run the `counter` example, enter the counter directory, and then use `make` to compile and link the Rust and C programs into the executable program `counter.rcompcert`. After that, use `make test` to test the output.

```
cd counter
make
make test
```