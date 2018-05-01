# PTX-superoptimizer

The best sort of read-me is [the paper](paper/main.pdf).

But if that's not appetizing, there are [some slides](https://docs.google.com/presentation/d/1YvI-1Ouz_cLraR2vBAQ-aJvS1K9qtkKSLA3amVI6aJk/edit?usp=sharing).

## Requirements and Installing

This is to install on Linux. TL;DR, get z3 and pyparsing; I use python3
and python2 is not supported.

z3 is required, but I didn't install it through pip.
Here are [z3's instructions](https://github.com/Z3Prover/z3#building-z3-using-make-and-gccclang),
and after this, I run the following to import z3 and note that I can in my shell prompt:
```bash
export PYTHONPATH=$PATH_TO_Z3/z3/build/python
export PATH=$PATH:$PATH_TO_Z3/z3/build/

export PS1="(z3 env) $PS1"
```

`pip install -r requirements.txt` gets you pyparsing, the other requirement.

I really recommend virtualenv, but you do you.
