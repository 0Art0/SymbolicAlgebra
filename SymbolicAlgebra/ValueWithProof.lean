/-
  This type bundles together a value of a certain type 
  together with a proof that it satisfies a certain property.

  It can be used to write algorithms that return values 
  that must satisfy certain defining properties.
-/
@[class] structure Prover {α : Type _} (p : α → Prop) :=
  value : α
  proof : p value

-- easier notation
notation "#[" v ":" T "]" " ~ " p => Prover (λ (v : T) => p)

-- examples
#check #[x : Nat] ~ (x + 5 > 0)

example : #[x : Nat] ~ (x + 5 = 10) :=
  {
    value := 5, 
    proof := rfl
  }

-- connection with existential quantifier
theorem valueWitness {α : Type _} {p : α → Prop} : (#[v : α] ~ p v) → (∃ v : α, p v) :=
  λ valPrf => ⟨valPrf.value, valPrf.proof⟩