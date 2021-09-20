import Mathlib.Data.Int.Basic

structure Rational where
  (num : ℤ)
  (den : ℤ)
  (nonZero : ¬(den = 0))

notation "ℚ" => Rational

