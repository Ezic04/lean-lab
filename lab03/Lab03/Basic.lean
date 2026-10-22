/- Lean course, scenario 03: first proofs -/

/- Acknowledgements.
   This scenario is essentially the exercise set from Theorem Proving in Lean 4,
   https://leanprover.github.io/theorem_proving_in_lean4/Propositions-and-Proofs/#Theorem-Proving-in-Lean-4--Propositions-and-Proofs--Exercises
-/

/- EXERCISE 1
   Prove the following identities.
   For each of the identities, try to do it (1) without tactics, (2) with basic tactics.
   Do not use the law of excluded middle before the "open Classical" line -/
section
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
   constructor
   ·  intro ⟨hp, hq⟩
      constructor <;> assumption
   ·  intro ⟨hq, hp⟩
      exact ⟨hp, hq⟩
example : p ∨ q ↔ q ∨ p :=
  let h_and_comm (x y: Prop) : x ∨ y → y ∨ x := fun hor => match hor with
    | .inl h => Or.inr h
    | .inr h => Or.inl h
  Iff.intro (h_and_comm p q) (h_and_comm q p)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  · intro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, hq, hr⟩
  · intro ⟨hp, hq, hr⟩
    exact ⟨⟨hp, hq⟩, hr⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  · rintro ((hp | hq) | hr)
    · exact .inl hp
    · exact .inr (.inl hq)
    · exact .inr (.inr hr)
  · rintro (hp | hq | hr)
    · exact .inl (.inl hp)
    · exact .inl (.inr hq)
    · exact .inr hr

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  intro ⟨hp, hqr⟩
  cases hqr with
  · sorry
  · sorry
  sorry

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry

example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry

end section

-- From now you can use the law of excluded middle
section
open Classical

variable (p q r : Prop)

-- em p gives p ∨ ¬p
#check em p
-- You can try also constructions: byCases or byContradiction

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry

end section
