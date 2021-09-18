# SymbolicAlgebra

Mathematical programs with proofs, in LEAN 4.

---

# Gosper's algorithm

The aim is to implement [Gosper's algorithm for indefinite hypergeometric summation](https://en.wikipedia.org/wiki/Gosper%27s_algorithm) with proof.

This means that when a [hypergeometric term](https://mathworld.wolfram.com/HypergeometricTerm.html) `t(n)` is given as input to the program, it should either return another hypergeometric term `s(n)` along with proof that it is the indefinite summation of `t(n)`, or return a proof that no closed form hypergeometric term that is the indefinite summation of `t(n)`.

## Background and Motivation

### Terminology

> Roughly, a hypergeometric sum is one in which the summand involves only factorials, polynomials, and exponential functions of the summation variable (from page 33 of the book `A = B`).

A *hypergeometric series* $\sum_{k \in \mathbb{Z} \\ k \geq 0} t_k$ is one in which the first term $t_0 = 1$, and the ratio of any consecutive terms is a rational function of the summation index, i.e.,

$$
\frac{t_{k+1}}{t_k} = \frac{P(k)}{Q(k)}
$$ 

where $P$ and $Q$ are fixed polynomials in $k$. The terms in a hypergeometric series are called *hypergeometric terms*. 

More concretely, a *hypergeometric term* is a function $t : \mathbb{N} \to K$ from the natural numbers to a field $K$, which satisfies $\frac{t(k+1)}{t(k)} = \frac{P(k)}{Q(k)}, \forall k \in \mathbb{N}$, where $P$ and $Q$ are fixed polynomials over the field $K$ (the requirement of $t(0) = 1$ can be relaxed as one can always rescale).

### Examples

(TO-DO)

### Indefinite summation

Consider a summation of the form 

$$
s_n = \sum_{k = 0}^{n-1} t_k
$$

where $t_k$ is a hypergeometric term that does not depend on $n$, i.e., the consecutive term ratio

$$
r(k) = \frac{t_{k+1}}{t_k}
$$

is a rational function of $k$ (ratio of two polynomials in $k$).


One can ask whether $s_n$ has a closed form that does not involve summation. This is analogous to finding the anti-derivative in the continuous case, where the derivative is replaced with a difference : the requirement now is that $s_n$ satisfies $s_{n+1} - s_n = t_n$.  

One can strengthen this further by asking whether there exists a *hypergeometric term* $z_n$ such that

$$
z_{n+1} - z_n = t_n
$$

If such a term $z_n$ can be found, then $s_n$ can be written as a hypergeometric term plus a constant.

### Examples

(TO-DO)

### Gosper's algorithm

Gosper's algorithm is a decision procedure for indefinite hypergeometric summation. 

That is, given a hypergeometric term $t_n$, Gosper's algorithm is capable of finding a hypergeometric term $z_n$ satisfying $z_{n+1} - z_n = t_n, \forall n \in \mathbb{N}$ if one exists (in which case $t_n$ is called *Gopser-summable*). The algorithm returns a negative answer **if and only if** no such $z_n$ exists.

The steps of the algorithm will be outlined in a separate document in this repository.

## References

1. [A = B](https://www2.math.upenn.edu/~wilf/AeqB.html)
2. [Gosper, R. William. "Decision procedure for indefinite hypergeometric summation." (the original paper)](https://www.pnas.org/content/pnas/75/1/40.full.pdf)


---