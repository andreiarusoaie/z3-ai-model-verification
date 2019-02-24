# Prerequisites

First, install Z3 from [this link](https://github.com/Z3Prover/z3/releases). The code here was tested with a locally compiled version of Z3. If you do not want to compile it, we recommend you to install version 4.8.4 or higher.

After the installation, make sure that the z3 command is available in your terminal:

```
-$ z3 --version
Z3 version 4.8.5 - 64 bit
```

**Optionally**, you can install [GNU Make](https://www.gnu.org/software/make/). GNU Make is available on Windows as well. This [link](http://gnuwin32.sourceforge.net/packages/make.htm) might be helpful.

# Running Z3

In order to run our examples, open your terminal and type the following commands:

```
-$ mkdir work
-$ cd work
-$ git clone https://github.com/andreiarusoaie/z3-ai-model-verification.git
-$ cd z3-ai-model-verification/experiments/cannibals_and_missionaries/correct-model
-$ z3 -v:10 -st  pfs.smt2 > pfs.out 2> pfs.err
```

The last command calls z3. The `-v:10` option sets the verbosity level to 10, while the `-st` option enables the statistics. In `pfs.out` we find the output of z3, and on `pfs.err` we find the errors thrown by the SMT solver.

