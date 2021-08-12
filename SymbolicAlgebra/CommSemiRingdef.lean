import SymbolicAlgebra.ValueWithProof

-- according to the mathlib4 comments, these two definitions
-- were a part of the LEAN3 core library

class Zero (α : Type u) where
  zero : α

instance [Zero α] : OfNat α (nat_lit 0) where
  ofNat := Zero.zero

class One (α : Type u) where
  one : α

instance [One α] : OfNat α (nat_lit 1) where
  ofNat := One.one

-- the definition of a semiring

class SemiRing (A : Type _) extends Zero A, One A, Add A, Mul A where
  addAssoc : ∀ a b c : A, (a + b) + c = a + (b + c)
  addComm : ∀ a b : A, a + b = b + a
  
  zeroAdd : ∀ a : A, 0 + a = a
  addZero : ∀ a : A, a + 0 = a

  mulAssoc : ∀ a b c : A, (a * b) * c = a * (b * c)
  mulComm : ∀ a b : A, a * b = b * a

  oneMul : ∀ a : A, 1 * a = a
  mulOne : ∀ a : A, a * 1 = a

  mulAdd : ∀ a b c : A, a * (b + c) = a * b + a * c
  addMul : ∀ a b c : A, (a + b) * c = a * c + b * c

  zeroMul : ∀ a : A, 0 * a = a
  mulZero : ∀ a : A, a * 0 = a

  σ : A → Nat
  QuotRem (a b : A) (hb : ¬(b = 0)) : >> (q, r) : A × A ~ 
                                      a = q * b + r ∧ (r = 0  ∨  σ r < σ b)