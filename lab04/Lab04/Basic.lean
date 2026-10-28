/- Lean course, lab scenario 04 -/

/- Acknowledgements.
   The exercises are originally by Leni Aniva, Abdalrhman Mohamed
   from the course https://perfect-math-class.leni.sh/, assignment 07.
-/

/- EXERCISE 1
   Prove the following four statements about Nat, the natural numbers.
   You are not allowed to use any tactics, except for possibly the French bracket ‹...›
   (The French bracket stands for "show ... from assumption".)

   Warning: We found this a very frustrating exercise. The statements are obvious,
   but finding all the necessary pieces and making them fit each other is far from trivial.
   Also, we find most of our solutions not really readable or particularly elegant.

   Some hints:
    - You may find it useful to browse Mathlib Nat reference
      https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Basic.html
    - Another useful way may be Loogle or asking your favourite LLM questions
      like "What is the Lean 4 statement that says that x <= x for x : Nat?"
-/

section
-- definition of `<`
#print Nat.lt
#print Nat.le

example (x : Nat) : x < x + 1 := Nat.le.refl

example (x : Nat) : x - 1 ≤ x :=
  match hp : x - 1 with
  | Nat.zero => Nat.zero_le x
  | Nat.succ n =>
    let m := n.succ
    have : 1 ≤ x :=
      have : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le n)
      have : n.succ ≤ x := hp ▸ (Nat.sub_le x 1)
      Nat.le_trans ‹1 ≤ m› ‹m ≤ x›
    have : n.succ + 1 = x := hp ▸ Nat.sub_add_cancel ‹1 ≤ x›
    Nat.le.intro ‹m + 1 = x›

example (x y : Nat) : x = y + 1 → x + 1 = y + 2 := congrArg Nat.succ

example (n : Nat) : 0 < n → n < 2 * n :=
  fun h_ne_zero =>
  Trans.trans (Nat.one_mul n).symm
    (Nat.mul_lt_mul_of_pos_right Nat.le.refl h_ne_zero)

end

/- EXERCISE 2
   Prove the same statements as in Exercise 1, but this time using basic tactics,
   such as exact, intro, rw, by_cases, apply, suffices, ...
   Do not use yet more advanced tactics such as simp, aesop, grind.

   You can follow the lines of your proofs from Exercise 1, simplify these proofs,
   or invent completely new ones. Aim for readability and elegancy of your solutions.
   (In most cases, our solutions here are much more readable than their Exercise 1
   counterparts.)
-/
section
example (x : Nat) : x < x + 1 := by
  exact Nat.lt_succ_self x

example (x : Nat) : x - 1 ≤ x := by
  exact Nat.sub_le x 1

example (x y : Nat) : x = y + 1 → x + 1 = y + 2 := by
  intro h
  rw [h]

example (n : Nat) : 0 < n → n < 2 * n := by
  intro h_ne_zero
  have h : 1 * n < 2 * n := Nat.mul_lt_mul_of_pos_right Nat.le.refl h_ne_zero
  rw [Nat.one_mul n] at h
  exact h

end

/- EXERCISE 3
  Prove the following logic tautologies using basic tactics.
  Our recommendations: constructor, intro, exact, cases.

  Law of excluded middle may be needed in some of them.
  (Recall: use `Classical.em r` to get `r ∨ ¬r`.)
-/
section
variable (α : Type) (p q : α → Prop) (r : Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  · intro hpq
    exact ⟨fun x => (hpq x).left, fun x => (hpq x).right⟩
  · sorry

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by sorry
example : α → ((∀ _x : α, r) ↔ r) := by sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by sorry
end
