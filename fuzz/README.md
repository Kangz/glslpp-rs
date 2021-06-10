# Fuzzing infrastructure
Uses [afl.rs](https://github.com/rust-fuzz/afl.rs) to fuzz the preprocessor.

# Setup

Taken from the rust-fuzz [book](https://rust-fuzz.github.io/book/afl/setup.html) 

## Requirements

### Tools

- C compiler
- make

### Platform

afl.rs works on x86-64 Linux and x86-64 macOS.

```sh
cargo install afl
```

# Fuzzing

To start fuzzing first build the fuzzing binary (everytime a changes is made the
binary must be recompiled)

``` shell
cargo afl build
```

Finally start fuzzing the binary with

``` shell
cargo afl fuzz -i in -o out target/debug/fuzz
```
