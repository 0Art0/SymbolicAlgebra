import SymbolicAlgebra.ValueWithProof
import Mathlib.Data.Nat.Basic

/-
An abstract class for types such as lists and arrays that can
be indexed, i.e., given an indexable type and a natural number, 
one can produce an element of a certain type.
-/
class Indexable (α : Type → Type _) where
  index {T : Type} [Inhabited T] : (α T) → ℕ → T

/-
A sequence of type `T` is a function from `ℕ` to `T`
(i.e., a sequence in the mathematical sense).
Sequences are implemented using `Indexable` types. 
-/
structure Sequence (T : Type) where
  seqtype : Type → Type _
  [indexable : Indexable seqtype]
  values : seqtype T

/-
A method for extracting the `n`th term of a sequence `s`.
-/
def seqIndex {T : Type} [Inhabited T] (s : Sequence T) (n : ℕ) : T := s.indexable.index (s.values) n

-- familiar notation for indexing into sequences
notation s "[[" n "]]" => seqIndex s n

/-
Special cases of Sequences, where every term after a number `cap` is
equal to the specified constant `c`.

Instead of specifying the `cap` and the fact that the sequence 
eventually becomes constant after `cap` as two different fields of the
structure, they are bundled into a single value-proof object.
This makes it easier to prove that `cap` satisfies the required property.
-/
structure ECSequence (T : Type) [Inhabited T] (c : T)
  extends Sequence T where
  eventuallyConstant : #[cap : ℕ] ~ (∀ n : ℕ, n ≥ cap → indexable.index values n = c)


section Instances
  /-
  If the input is within bounds, the list is indexed the usual way.
  Otherwise, the default element of the inhabited type is returned.

  def listIndex {T : Type} [Inhabited T] 
    (l : List T) (n : ℕ) : T :=
    match l, n with
      | [], _ => Inhabited.default
      | (a::as), 0 => a
      | (a::as), (n+1) => listIndex as n

  instance : Indexable List := ⟨listIndex⟩

  -/

  /-
    Abbreviation for functions from `ℕ` to an arbitrary type `T`.
  -/
  def FunctionSeq := (λ T : Type => (ℕ → T))

  instance : Indexable FunctionSeq := ⟨λ f => f⟩
  
  /-
  A program-with-proof that takes in a list of type `List T` and 
  a natural number, and returns an element of type `T` along with
  a proof that the output is the default value of `T` if `n` is 
  out of bounds.
  -/
  def finiteListIndex {T : Type} [Inhabited T]
    (l : List T) (n : ℕ) : #[t : T] ~ (n ≥ (List.length l) → t = Inhabited.default)
 :=
    match l, n with
      | [], n => {value := Inhabited.default, proof := λ h => rfl}
      | (a::as), 0 => {value := a, proof := 
          λ h => False.elim (
            have : List.length (a::as) = 0 := Nat.eq_zero_of_le_zero h;
            have : 0 = Nat.succ (List.length as) := by {simp at this};
            Nat.noConfusion this
      )}
      | (a::as), (n+1) => {value := (finiteListIndex as n).value, proof := λ h =>
        have : n ≥ List.length as := Nat.le_of_succ_le_succ h;
        (finiteListIndex as n).proof this
      }

  instance indexableList : Indexable List := ⟨λ l => λ n : ℕ => (finiteListIndex l n).value⟩

  /-
  A function to generate an eventually constant sequence from a list.
  -/
  def ECSequence.mkList {T : Type} [Inhabited T] (l : List T) : ECSequence T Inhabited.default := 
    {
      seqtype := List,
      indexable := indexableList, 
      values := l, 
      eventuallyConstant := {value := List.length l,                            proof := λ n h =>  (by {
        simp
        have : (finiteListIndex l n).value = Indexable.index l n := rfl;
        rw [← this]
        exact (finiteListIndex l n).proof h
        })
      }
    }

  /-
  Coercion from ECSequences to Sequences.
  -/
  instance (T : Type) [Inhabited T] {c : T} : Coe (ECSequence T c) (Sequence T) :=
  ⟨λ es => {seqtype := es.seqtype, indexable := es.indexable, values := es.values}⟩

  /-
    A method for extracting the `n`th term of an eventually constant sequence `s`.
  -/
  def ECSeqIndex {T : Type} [Inhabited T] {c : T} (ecs : ECSequence T c) (n : ℕ) : T := ecs.indexable.index (ecs.values) n


end Instances


section Examples

  def testSeq0 : Sequence ℕ := ⟨FunctionSeq, λ n : ℕ => n⟩

  def testSeq1 : Sequence ℕ := ⟨List, [1, 2, 3]⟩

  def testSeq2 : ECSequence ℕ 0 := ECSequence.mkList [4, 5, 6, 7, 8, 9, 10]

  #eval testSeq0[[10]]
  #eval testSeq1[[2]]
  #eval ECSeqIndex testSeq2 1

end Examples
