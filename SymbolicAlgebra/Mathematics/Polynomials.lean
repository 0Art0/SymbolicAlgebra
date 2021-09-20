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

variable {R : Type} [CommRing R]
variable {X : String}

/-
A function to extract the `n`th coefficient from a polynomial `p`.
-/
def extractCoef (p : Polynomial R X) (n : ℕ) := ECSeqIndex p.coefs n

notation p "[" n "]" => extractCoef p n

/-
Determines the degree of a polynomial, given that it is less than a number `b`.
-/
def degreeBound (p : Polynomial R X) [eqZero : ∀ r : R, Decidable (r = 0)] (b : ℕ) : ℕ :=
    match b with
        | 0 => 0 -- an arbitrary value for the degree of the zero polynomial
        | (n+1) => if p[n+1] = 0 then degreeBound p n else (n+1)

/-
Determines the degree of a polynomial.
-/
def degree (p : Polynomial R X) [eqZero : ∀ r : R, Decidable (r = 0)] := degreeBound p p.coefs.eventuallyConstant.value

/-
An upper bound for the degree of a polynomial.
-/
def bound (p : Polynomial R X) : ℕ := p.coefs.eventuallyConstant.value

/-
The definition of the sum of two polynomials.
-/
def add (p q : Polynomial R X) : Polynomial R X := {coefs := ECSequence.mkFunction (λ n : ℕ => p[n] + q[n]) (max (bound p) (bound q))}

/-
Sum of a list of elements of a ring.
-/
def sum (l : List R) : R :=
    l.foldl (init := 0) (·+·)

/-
The definition of the product of two polynomials.
-/
def mul (p q : Polynomial R X) : Polynomial R X := {coefs := ECSequence.mkFunction (λ n : ℕ => sum ((List.range (n+1)).map (λ k : ℕ => p[k] * q[n-k]))) (bound p * bound q)
}

instance : Add (Polynomial R X) := ⟨add⟩
instance : Mul (Polynomial R X) := ⟨mul⟩


end Polynomial