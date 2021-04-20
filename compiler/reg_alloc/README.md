## How to Run

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

