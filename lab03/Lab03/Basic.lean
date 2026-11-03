/- Lean course, scenario 03: first proofs -/

/- Acknowledgements.
   This scenario is essentially the exercise set from Theorem Proving in Lean 4,
   https://leanprover.github.io/theorem_proving_in_lean4/Propositions-and-Proofs/#Theorem-Proving-in-Lean-4--Propositions-and-Proofs--Exercises
-/

/- EXERCISE 1
   Prove the following identities.
   For each of the identities, try to do it (1) without tactics, (2) with basic tactics.
   Do not use the law of excluded middle before the "open Classical" line -/
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
   constructor
   ·  intro ⟨hp, hq⟩
      constructor <;> assumption
   ·  intro ⟨hq, hp⟩
      exact ⟨hp, hq⟩

example : p ∨ q ↔ q ∨ p :=
  let h_and_comm (x y: Prop) : x ∨ y → y ∨ x
    | .inl hx => Or.inr hx
    | .inr hy => Or.inl hy
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
  · intro ⟨hp, hqr⟩
    exact hqr.elim (.inl ⟨hp, ·⟩) (.inr ⟨hp, ·⟩)
  · rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
    · exact ⟨hp, .inl hq⟩
    · exact ⟨hp, .inr hr⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  · rintro (hp | ⟨hq, hr⟩)
    · exact ⟨.inl hp, .inl hp⟩
    · exact ⟨.inr hq, .inr hr⟩
  · rintro ⟨hp | hq, hp | hr⟩
    · exact .inl hp
    · exact .inl hp
    · exact .inl hp
    · exact .inr ⟨hq, hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  · exact fun curr ⟨hp, hq⟩ => curr hp hq
  · exact fun uncurr hp hq => uncurr ⟨hp, hq⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  · exact fun hr => ⟨hr ∘ .inl, hr ∘ .inr⟩
  · exact fun ⟨hp, hq⟩ hpq => hpq.elim hp hq

theorem not_or_iff_and_not {p q} : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  · exact fun hpq => ⟨hpq.imp .inl, hpq.imp .inr⟩
  · exact fun ⟨hp, hq⟩ hpq => hpq.elim hp hq

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun hpq ⟨hp, hq⟩ => hpq.elim (· hp) (· hq)

example : ¬(p ∧ ¬p) := fun ⟨hp, hnp⟩ => hnp hp

example : p ∧ ¬q → ¬(p → q) := fun ⟨hp, hnq⟩ hpq => hnq (hpq hp)

example : ¬p → (p → q) := fun hnp hp => absurd hp hnp

example : (¬p ∨ q) → (p → q) := fun hpq => hpq.elim (flip absurd) (Function.const p)

example : p ∨ False ↔ p := by
  constructor
  · exact fun hpf => hpf.elim id False.elim
  · exact .inl

example : p ∧ False ↔ False := by
  constructor
  · exact And.right
  · exact fun hf => ⟨hf.elim, hf⟩

example : (p → q) → (¬q → ¬p) := flip Not.imp


-- From now you can use the law of excluded middle
-- variable (p q r : Prop)

-- em p gives p ∨ ¬p
#check Classical.em p
-- You can try also constructions: byCases or byContradiction

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := fun hpqr =>
  have h_pos := fun hp => (hpqr hp).elim (Or.inl ∘ Function.const p) (Or.inr ∘ Function.const p)
  have h_neg := fun hnp => Classical.byContradiction fun hnpq =>
    have ⟨hnq, _⟩ := not_or_iff_and_not.mp hnpq
    have hpq : p → q := (absurd · hnp)
    hnq hpq
  Classical.byCases (p := p) h_pos h_neg

example : ¬(p ∧ q) → ¬p ∨ ¬q := fun hn_pq =>
  have hp_pos : p → ¬p ∨ ¬q := fun hp => Or.inr (hn_pq ⟨hp, ·⟩)
  Classical.byCases (p := p) hp_pos Or.inl

example : ¬(p → q) → p ∧ ¬q := fun hn_pq =>
  have hp : p :=
    Classical.byContradiction fun hnp =>
    have h_pq : p → q := fun hp => absurd hp hnp
    hn_pq h_pq
  have hnq : ¬q := hn_pq ∘ Function.const p
  ⟨hp, hnq⟩

theorem or_of_imp : (p → q) → (¬p ∨ q) := fun h_pq =>
  Classical.byCases (p := p) (Or.inr ∘ h_pq) Or.inl

example : (¬q → ¬p) → (p → q) := fun h_cpos hp =>
  have h_or := or_of_imp (¬q) (¬p) h_cpos
  h_or.elim Classical.not_not.mp (absurd hp)

example : p ∨ ¬p := Classical.byContradiction fun h =>
  have h_np_nnp := not_or_iff_and_not.mp h
  h_np_nnp.right h_np_nnp.left

example : (((p → q) → p) → p) := fun h_imp =>
  Classical.byContradiction fun hnp =>
  have hpq : p → q := (absurd · hnp)
  absurd (h_imp hpq) hnp
