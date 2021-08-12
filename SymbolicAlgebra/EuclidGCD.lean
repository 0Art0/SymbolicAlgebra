import SymbolicAlgebra.ValueWithProof

notation "ℕ" => Nat

open Nat

def QuotRem (a b : ℕ) (hbpos : ¬(b = 0)) :
  >> (q, r) : ℕ × ℕ ~ a = b * q + r  ∧  r < b :=
  match a, b, hbpos with
    | _, zero, h    => {value := (0, 0), proof := False.elim (h rfl) }
    | zero, succ n, _ => {value := (0, 0), proof := ⟨rfl, zeroLtSucc _⟩}  
    | succ m, succ n, h => 
      match QuotRem m (succ n) h with
        | ⟨(q, r), pf⟩ => 
          if succ r = succ n then
            {value := (succ q, zero), proof := ⟨sorry, zeroLtSucc _⟩}
          else
            {value := (q, succ r), proof := ⟨sorry, sorry⟩}

notation a " /% " b => QuotRem a b Nat.noConfusion

#reduce 11 /% 3


def divides (a b : ℕ) := ∃ c : ℕ, (b = a * c)

infix:100 " ∣ " => divides

def commonDivisor (a b : ℕ) (c : ℕ) := c ∣ a  ∧  c ∣ b

def isGCD (a b : ℕ) (d : ℕ) := (commonDivisor a b) d ∧ 
                       ∀ c, (commonDivisor a b) c → c ∣ d


def EuclidGCD 
  (bound a b : ℕ) 
  (hbound : bound > a + b) :
  >> d : ℕ ~ (isGCD a b) d :=
  match a, b with
    | zero, zero => {value := zero, proof := sorry}
    | succ m, zero => {value := succ m, proof := ⟨⟨⟨succ zero, sorry⟩, ⟨zero, rfl⟩⟩, sorry⟩}
    | m, succ n =>
    match bound with
      | zero => {value := zero, proof := False.elim sorry}
      | succ bnd =>
      if m ≥ (succ n) then
        match QuotRem m (succ n) sorry with
        | ⟨(q, r), pf⟩ =>
          match (EuclidGCD bnd (succ n) r sorry) with
          | ⟨v, p⟩ => ⟨v, sorry⟩
      else
        match (EuclidGCD bnd (succ n) m sorry) with
          | ⟨v, p⟩ => ⟨v, sorry⟩

#reduce (EuclidGCD 20 17 10 sorry)