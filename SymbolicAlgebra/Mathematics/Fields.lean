import Mathlib.Algebra.Ring.Basic

/-
Definition of a `Field` as a commutative ring
with multiplicative inverses for non-zero elements
-/
class Field (F : Type) extends CommRing F, Inv F where
  (mulInv (a : F) : ¬(a = 0) → a * a⁻¹ = 1)

