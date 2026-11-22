-- ## Section 1: Natural numbers

namespace MyNats

-- Recall the definition of natural numbers from last week.

inductive Nat : Type where
  | zero : Nat
  | succ (n : Nat) : Nat

open MyNats.Nat

def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)

local infix:65 (priority := high) " + " => add

-- Define the less-than-or-equal relation as an inductive predicate.

inductive le (n : Nat) : Nat → Prop
  | refl     : le n n
  | step {m} : le n m → le n (succ m)

local infix:50 (priority := high) " ≤ " => le

/- EXERCISE 1 -/
/- Prove the following four theorems. -/

-- 1. Adding a natural number cannot decrease a number.
theorem le_add (n k : Nat) :
    n ≤ n + k := by
  sorry

-- 2. Addition preserves inequalities.
theorem le_add_mono (n m k : Nat) :
    n ≤ m → n + k ≤ m + k := by
  sorry

-- 3. If n ≤ m, then m can be written as n + k for some k.
theorem le_exists_add (n m : Nat) :
    n ≤ m → ∃ k, m = n + k := by
  sorry

-- 4. If m = n + k for some k, then n ≤ m.
theorem exists_add_le (n m : Nat) :
    (∃ k, m = n + k) → n ≤ m := by
  sorry

end MyNats

-- ## Section 2: Custom predicates

/- EXERCISE 2 -/
/- Define a predicate for even natural numbers inductively, then complete the proofs. -/

inductive MyEven : Nat → Prop where
  -- Define the constructors.

example : MyEven 6 := by
  sorry

theorem even_add {n m : Nat} :
    MyEven n → MyEven m → MyEven (n + m) := by
  sorry

/- EXERCISE 3 -/
/- The predicate `Subseq xs ys` below states that `xs` is a subsequence of `ys`:
   its elements occur in the same order, but need not be consecutive.
   Prove the example and the four theorems below, including transitivity. -/

inductive Subseq {α : Type} :
    List α → List α → Prop where
  | nil : Subseq [] []
  | skip {x : α} {xs ys : List α} : Subseq xs ys → Subseq xs (x :: ys)
  | keep {x : α} {xs ys : List α} : Subseq xs ys → Subseq (x :: xs) (x :: ys)

example : Subseq [1, 3] [1, 2, 3] := by
  sorry

theorem subseq_refl {α : Type} (xs : List α) :
    Subseq xs xs := by
  sorry

theorem subseq_length {α : Type}
    (xs ys : List α) :
    Subseq xs ys → xs.length ≤ ys.length := by
  sorry

theorem subseq_eq {α : Type}
    (xs ys : List α) :
    Subseq xs ys →
    xs.length = ys.length →
    xs = ys := by
  sorry

theorem subseq_trans {α : Type}
    (xs ys zs : List α) :
    Subseq xs ys →
    Subseq ys zs →
    Subseq xs zs := by
  sorry

/- EXERCISE 4 -/
/- A palindrome is a list that reads the same forwards and backwards.
   `Palindrome₁` expresses this using `List.reverse`.
   Give an inductive definition of `Palindrome₂` without using `List.reverse`,
   then prove the example and the two theorems below. -/

def Palindrome₁ {α : Type} (xs : List α) : Prop :=
  xs.reverse = xs

inductive Palindrome₂ {α : Type} : List α → Prop where
  -- Define the constructors without using List.reverse.

example : Palindrome₂ [1, 2, 3, 2, 1] := by
  sorry

theorem palindrome_append_reverse {α : Type}
    (xs : List α) :
    Palindrome₂ (xs ++ xs.reverse) := by
  sorry

theorem palindrome₂_implies₁ {α : Type}
    (xs : List α) :
    Palindrome₂ xs → Palindrome₁ xs := by
  sorry

/- EXERCISE 5 -/
/- Formalize the Collatz conjecture. You may look up its statement online.
   Define any auxiliary functions or inductive predicates you need, then write
   `theorem collatz : ... := by sorry`, replacing `...` with the conjecture.
   Hint: An auxiliary inductive predicate `CollatzHalts : Nat → Prop` may help.
   Make sure the statement applies to every positive natural number.
   If you are feeling lucky, try `grind` or an AI-powered tool to look for a proof. -/

/- EXERCISE 6 -/
/- Complete the proof of the pumping lemma from the lecture.
   You may introduce helper lemmas. -/

inductive Alphabet : Type where
  | A
  | B

abbrev Word := List Alphabet

inductive RegularExpression : Type where
  | Eps
  | Letter (letter : Alphabet)
  | Concat (left right : RegularExpression)
  | Union (left right : RegularExpression)
  | Star (expr : RegularExpression)

open RegularExpression

inductive Recognizes : RegularExpression → Word → Prop
  | EpsR : Recognizes Eps []
  | LetterR : Recognizes (Letter letter) [letter]
  | UnionL (h : Recognizes left word) : Recognizes (Union left right) word
  | UnionR (h : Recognizes right word) : Recognizes (Union left right) word
  | ConcatR
      (hLeft : Recognizes left wordLeft)
      (hRight : Recognizes right wordRight) :
      Recognizes (Concat left right) (wordLeft ++ wordRight)
  | StarEps : Recognizes (Star expr) []
  | StarStep
      (hHead : Recognizes expr wordHead)
      (hTail : Recognizes (Star expr) wordTail) :
      Recognizes (Star expr) (wordHead ++ wordTail)

/-! ## The pumping lemma -/

def repeatWord (word : Word) : Nat → Word
  | 0 => []
  | n + 1 => word ++ repeatWord word n

theorem pumpingLemma :
    ∀ expr : RegularExpression,
      ∃ k : Nat,
        ∀ word : Word,
          Recognizes expr word ∧ word.length > k →
            ∃ word₁ word₂ word₃ : Word,
              word = word₁ ++ word₂ ++ word₃ ∧
              word₂ ≠ [] ∧
              ∀ n : Nat, Recognizes expr (word₁ ++ repeatWord word₂ n ++ word₃) := sorry

/- EXERCISE 7 (Challenging, optional) -/
/- Prove that Palindrome₁ implies Palindrome₂. -/
/- Hint: Recall the idea of fuel from the first lecture. -/

theorem palindrome₁_implies₂ {α : Type}
    (xs : List α) :
    Palindrome₁ xs → Palindrome₂ xs := by
  sorry
