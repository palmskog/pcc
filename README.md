# PCC






A light-weight approach for certification of monitor inlining for
sequential Java bytecode using proof-carrying code, formalized
in Coq.

## Meta

- Author(s):
  - Andreas Lundblad (initial)
  - Karl Palmskog
- License: [Unknown](LICENSE)
- Compatible Coq versions: 8.10 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) 1.9.0 or later (`ssreflect` suffices)
- Coq namespace: `PCC`
- Related publication(s):
  - [A Proof Carrying Code Framework for Inlined Reference Monitors in Java Bytecode](https://arxiv.org/abs/1012.2995) 

## Building instructions

``` shell
git clone https://github.com/palmskog/pcc.git
cd pcc
make   # or make -j <number-of-cores-on-your-machine>
```

## Documentation

The [paper][arxiv-paper] has more information about the approach.

[arxiv-paper]: https://arxiv.org/abs/1012.2995
