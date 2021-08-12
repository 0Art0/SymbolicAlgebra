/-
  This type bundles together a value of a certain type 
  together with a proof that it satisfies a certain property.

  It can be used to write algorithms that return values 
  that must satisfy certain defining properties.
-/
structure ValueWithProof {α : Type _} (p : α → Prop) :=
  value : α
  proof : p value

-- easier notation
-- the triangle is typed as `\rhd`
notation ">>" v ":" T " ~ " p => ValueWithProof (λ (v : T) => p)

-- an example
#check >> x : Nat ~ x.succ > 0