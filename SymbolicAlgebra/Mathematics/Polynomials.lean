import SymbolicAlgebra.ValueWithProof
import SymbolicAlgebra.Mathematics.Sequences
import Mathlib.Algebra.Ring.Basic

/-
The default element of a commutative ring is defined to be `0`.
-/
instance (R : Type) [CommRing R] : Inhabited R where
    default := 0

/-
A polynomial over a commutative ring `R` is defined to be an
eventually constant sequence of elements of `R`.

The sequence eventually takes the value `0`, since it is the default value of `R`.

The parameter `X` is the indeterminate of the polynomial ring.
-/
structure Polynomial (R : Type) [CommRing R] (X : String) where
    (coefs : ECSequence R 0)

section Polynomial

variable (R : Type) [CommRing R]
variable (X : String)

/-
A function to extract the `n`thcoefficient from a polynomial `p`.
-/
def extractCoef (p : Polynomial R X) (n : ℕ) := ECSeqIndex p.coefs n

notation p "[" n "]" => extractCoef p n

/-

-/

end Polynomial