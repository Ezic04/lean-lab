import Mathlib
/- Lab scenario 07 -/

/- Exercise 1 : subtyping -/

/- a) Write a function which conforms to this type.
   Write two versions: one that does the intended meaning,
   returning the minimum.
   Second one that always returns 0 -/
def upperBound (x y : Nat) : { z // z ≤ x ∧ z ≤ y } :=
  ⟨min x y, le_min_iff.mp le_rfl⟩

def upperBound_fake (x y : Nat) : { z // z ≤ x ∧ z ≤ y } :=
  ⟨0, Nat.zero_le x, Nat.zero_le y⟩

/- b) Write the same function, but with the return type that
      really says that the function returns minimum. -/

def upperBound_real (x y : Nat) : { z // z ∈ ({x, y} : Set ℕ) ∧ z ≤ x ∧ z ≤ y } :=
  ⟨min x y, min_choice x y, le_min_iff.mp le_rfl⟩

/- Exercise 2 : sets -/
section
variable (α : Type) (s t u : Set α)

/- Fill in the following sorries. The first one was in the lecture. -/
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro _ ⟨hs, ht | hu⟩
  · exact .inl ⟨hs, ht⟩
  · exact .inr ⟨hs, hu⟩

example : s ∩ (t ∪ u) ⊇ s ∩ t ∪ s ∩ u := by
  rintro _ (⟨hs, ht⟩ | ⟨hs, hu⟩)
  · exact ⟨hs, .inl ht⟩
  · exact ⟨hs, .inr hu⟩

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro _ ⟨⟨hs , ht⟩, hu⟩
  exact ⟨hs, (Or.elim · ht hu)⟩

example : (s \ t) \ u ⊇ s \ (t ∪ u) := by
  rintro a ⟨hs, htu⟩
  obtain ⟨ht, hu⟩ := not_or.mp htu
  exact ⟨⟨hs,  ht⟩, hu⟩

end

/- Exercise 3: Image, preimage -/
section
variable (f : α → β)
variable (t₁ t₂ t : Set β)

/- Fill in the sorries below -/
example : f ⁻¹' (t₁ ∪ t₂) = f ⁻¹' t₁ ∪ f ⁻¹' t₂ := rfl

example : f '' (f ⁻¹' t) ⊆ t := by
  rintro b ⟨a, hp, hi⟩
  exact hi ▸ hp

end
