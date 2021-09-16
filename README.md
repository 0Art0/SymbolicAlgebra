# SymbolicAlgebra

Mathematical programs with proofs, in LEAN 4.

# Gosper's algorithm

The aim is to implement [Gosper's algorithm for indefinite hypergeometric summation](https://en.wikipedia.org/wiki/Gosper%27s_algorithm) with proof.

This means that when a hypergeometric term `t(n)` is given as input to the program, it should either return another hypergeometric term `s(n)` along with proof that it is the indefinite summation of `t(n)`, or return a proof that no closed form hypergeometric term that is the indefinite summation of `t(n)`.

---
