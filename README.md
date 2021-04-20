# ECE553Project

Group members:

Tianle Zhang (tz94), Hao Jiang (hj110) and Yuchuan Li (yl645).

### HW1: lexer
Please see the directory "compiler/lexer".

### HW2: parser
Please see the directory "compiler/parser".

### HW3: semantic analysis
Please see the directory "compiler/semanalysis".

### HW4: IR

Please see the directory "compiler/ir".

### HW5: Instruction Selection

Please see the directory "compiler/ins_sel".

### Liveness, Register Allocation, Working Compiler

Please see the directory "compiler/reg_alloc".



## How to Run
```shell
cd ece553project/compiler/reg_alloc
```

To run a single test case:

```shell
./autotest.sh xxx.tig
```

To run the entire test suit:

```
./autotest.sh 2>&1 >result.out
```

**Generated files:**

`xxx.out` -- Message produced during the compilation, including compile errors if the tiger code is wrong.

`xxx.s` -- Generated MIPS assemly without library functions in `runtime.s`.

`xxx.tmp.s` -- `xxx.s` combined with `runtime.s` & `sysspim.s`. Can be executed by the command:

```
spim -file xxx.tmp.s
```
