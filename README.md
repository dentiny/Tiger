# ECE553Project

### Contribution:

Tianle Zhang(tz94): [TianleZhang](https://github.com/UOETianleZhang)

Hao Jiang(hj110): [HaoJiang](https://github.com/dentiny)

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
Install SML-nj and related packages:
```
sudo apt-get install smlnj
sudo apt-get install ml-lex
sudo apt-get install ml-yacc
```

The final working compiler is at compiler/reg_alloc. To compile and run in REPL:
```
cd compiler/reg_alloc
CM.make "sources.cm";
Main.compile <your-tiger-file>
```

To run a single test case:

```
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
