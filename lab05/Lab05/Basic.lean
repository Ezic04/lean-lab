/- Lean course, lab scenario 05 -/

/- Acknowledgements.
   This is a compilation (with some additions) of the exercises from three sources:
   by Sebastian Ullrich, https://github.com/IPDSnelting/tba-2022, set 4;
   by Leni Aniva, Abdalrhman Mohamed, https://perfect-math-class.leni.sh/, assignment 08.
   by Benjamin C. Pierce et al. https://softwarefoundations.cis.upenn.edu/
   -/


/-Here are the definitions from the lecture-/

def append (x : List a ) (y : List a) : List a :=
  match x with
  | .nil => y
  | .cons first tail => .cons first (append tail y)

def reverse (x : List a) : List a :=
  match x with
  | .nil => .nil
  | .cons x xs => append (reverse xs) [x]

/- EXERCISE 1-/
/- Proof the following two lemmas from the lecture-/

theorem append_nil (l : List a) : append l .nil = l := by
  induction l with
  | nil => rfl
  | cons x xs hi =>
    rw [append, hi]

theorem append_assoc (l₁ l₂ l₃ : List a) :
  append l₁ (append l₂ l₃) = append (append l₁ l₂) l₃ := by
  induction l₁ with
  | nil => rfl
  | cons x xs hi =>
    rw [append, hi, ←append, ←append]

namespace MyNats

/-
  The goal of the following exercises is to prove from scratch a number of very basic
  properties of natural numbers. Because all of them are already proven in Mathlib,
  and we do not want to look there, we are going to define our own type of natural numbers
  and work on it.
-/


-- A natural number is a zero or a successor of a natural number.
-- This definition will result in almost all proofs below being inductive.
inductive Nat : Type where
  | zero : Nat
  | succ (n : Nat) : Nat

open Nat -- linter here complains that Nat is ambiguous, let's ignore it

-- We now inductively define addition, multiplication, and less-or-equal.
def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)

-- With this command we add a notation for `add`. From now on we will be able to write `m + n` for
-- `add m n`. The 65 denotes how strongly the operator should bind to what's adjacent to it.
-- The `priority` means that Lean will prefer it over the built-in `+`.
infix:65 (priority := high) " + " => add

def mul (m n : Nat) : Nat :=
  match n with
  | zero   => zero
  | succ n => (mul m n) + m

-- We also want a notation for `mul`, with a higher binding strength than addition so that
-- `a + b * c` means `a + (b * c`)`.
infix:70 (priority := high) " * " => mul

/- EXERCISE 2
   Prove the following statements about addition and its interaction with <=.
   You can use tactics, we particularly recommend induction, rw, apply/exact.
   Try experimenting with simp, but think about what it is going to do before
   you run it. Try solving exercises with and without it. Try marking some lemmas with @[simp].
   Remember that exact? and apply? may give you useful hints.
-/
@[simp] theorem zero_add : zero + n = n := by
  induction n with
  | zero => rfl
  | succ n hi =>
    rw [add, hi]

-- We now mark that add and mul can be unfolded, when you use `simp`
attribute [simp] add mul

/- Prove the following two statements:
   - choose wisely which variable should be the base of the induction
   - add auxiliary lemmas if needed
-/

theorem add_assoc : (m + n) + k = m + (n + k) := by
  induction k with
  | zero => rfl
  | succ k hi =>
    rw [add, hi, ←add, ←add]

theorem one_comm (a b : Nat) : a.succ + b = a + b.succ := by
  induction b with
  | zero =>
    rw [add, add]
    rfl
  | succ c hi =>
    rw [add, hi, ←add]

theorem add_comm : n + m = m + n := by
  induction m with
  | zero =>
    rw [zero_add]
    rfl
  | succ m hi =>
    rw [add, hi, ←add, one_comm]

/- EXERCISE 3
   Prove the following statements about multiplication.
   Again, it is useful to think a bit about which variable the induction should apply to,
   sometimes you might need to use an auxiliary lemma.
-/

def one := succ zero

@[simp] theorem mul_zero {n} : n * zero = zero := by
  induction n with
  | zero => rfl
  | succ n hi => rw [mul]

@[simp] theorem zero_mul {n} : zero * n = zero := by
  induction n with
  | zero => rfl
  | succ n hi =>
    rw [mul, hi]
    rfl

@[simp] theorem mul_one : m * one = m := by
  induction m with
  | zero => rfl
  | succ m hi =>
    rw [one, mul, mul_zero, zero_add]

theorem mul_add {a b c} : a * (b + c) = a * b + a * c := by
  induction c with
  | zero =>
    rw [mul_zero]
    rfl
  | succ c hi =>
    rw [mul, add, mul, hi, add_assoc]

theorem mul_assoc : (m * n) * k = m * (n * k) := by
  induction k with
  | zero =>
    repeat rw [mul_zero]
  | succ k hi =>
    rw [mul, hi, mul, mul_add,]

theorem succ_mul : n.succ * m = n * m + m := by
  induction m with
  | zero =>
    repeat rw [mul_zero]
    rfl
  | succ m hi =>
    rw [mul, hi, mul, add, add, add_assoc, @add_comm m n, ←add_assoc]

theorem mul_comm {m n} : m * n = n * m := by
  induction n with
  | zero =>
    rw [mul_zero, zero_mul]
  | succ n hi =>
    rw [mul, succ_mul, hi]

@[simp] theorem one_mul {n} : one * n = n := mul_comm.trans mul_one

theorem add_mul {a b c} : (b + c) * a = b * a + c * a := by
  calc (b + c) * a
    _ = a * (b + c) := mul_comm
    _ = a * b + a * c := mul_add
    _ = b * a + c * a := by simp only [mul_comm]

theorem mul_succ : m * n.succ = n * m + m := mul_comm.trans succ_mul

theorem add_left_comm {a b c} : a + (b + c) = b + (a + c) := by
  rw [←add_assoc, @add_comm a b, add_assoc]

/-EXERCISE 4
  We define below `factorial` and `fibonacci` in two ways: using simple recursion and using an accumulator.
  Prove that the definitions return the same value. -/

def factorial : Nat → Nat
  | zero => one
  | succ n => succ n * factorial n

def factorialAux : Nat → Nat → Nat
  | zero, acc => acc
  | succ n, acc => factorialAux n (acc * succ n)

def factorial2 (n : Nat) : Nat := factorialAux n one

theorem factorialAux_eq
  : factorialAux n acc = acc * factorial n := by
  induction n generalizing acc with
  | zero =>
    simp [factorialAux, factorial]
  | succ n hi =>
    rw [factorialAux, hi, factorial, mul_assoc]

theorem factorial2_correct (n : Nat) : factorial2 n = factorial n := by
  induction n with
  | zero => rfl
  | succ n hi =>
    rw [factorial2] at hi
    rw [factorial2, factorialAux, one_mul, factorial, ←hi, factorialAux_eq, hi]

def fibonacci : Nat → Nat
  | zero => zero
  | succ zero => one
  | succ (succ n) => fibonacci n + fibonacci (succ n)

def fibonacciAux : Nat → Nat → Nat → Nat
  | zero, a, _ => a
  | succ n, a, b => fibonacciAux n b (a + b)

def fibonacci2 (n : Nat) : Nat := fibonacciAux n zero one

theorem fibonacciAux_eq : ∀ n a b, fibonacciAux n.succ a b = a * fibonacci n + b * fibonacci n.succ
  | zero, a, b => by
    simp [fibonacciAux, fibonacci]
  | succ zero, a, b => by
    simp [fibonacciAux, fibonacci]
  | succ (succ n), a, b => by
    rw [fibonacciAux, fibonacciAux_eq, @fibonacci.eq_3 n.succ, mul_add, add_mul, add_left_comm]

theorem fibonacci2Correct (n : Nat) : fibonacci2 n = fibonacci n := by
  induction n with
  | zero => rfl
  | succ n hi =>
    rw [fibonacci2] at hi
    simp [fibonacci2, fibonacciAux_eq]

/- EXERCISE 5
   The following predicate defines that a number is even.
   Prove that 0 is even and that if n is even, then so is n + 2.

   /- HINTS :
   (a) This does not require induction.
   (b) If we have a value `h : ∃x, φ(x)`, then `let ⟨k, hk⟩ := h` allows us to extract
       a specific `k` together wiht a proof that `φ(k)`
   (c) If we want to proof `∃x, φ(x)`, we need to find a `k` that satisfies `φ`, and use the tactic
       `exists k`, which will leave us with proving `φ(k)`. -/
-/

def two := one.succ
def Even : Nat → Prop := fun n => ∃ k : Nat, n = two * k

theorem zero_even: Even zero := ⟨zero, rfl⟩

theorem even_step : ∀ n : Nat, Even n → Even (n + two)
  | zero, _ => ⟨one, rfl⟩
  | succ n, ⟨m , hm⟩ =>
    have h : n.succ + two = two * m.succ := by
      rw [hm, mul_succ, mul_comm]
    ⟨m.succ, h⟩

/-EXERCISE 6 (*)-/

/- Prove the following lemma-/
/- HINT: You will need to use induction and cases-/
/- If you have in context  `h : zero = m.succ` you can use `contradiction` to finish the `proof`-/
/- If you have in context `h : n.succ = m.succ` you can use `simp at h` to obtain `n = m`
   (you can also use `Nat.succ.inj`)-/

#check Nat.succ.inj

theorem succ2_ne_self : ∀ (n : Nat), n.succ.succ ≠ n
  | zero => Nat.noConfusion
  | succ zero => Nat.noConfusion ∘ Nat.succ.inj
  | succ n => succ2_ne_self n ∘ Nat.succ.inj

theorem mul_two_inj (n m : Nat) (h : two * n = two * m) : n = m := by
  induction n generalizing m with
  | zero =>
    simp [two, succ_mul] at h
    induction m with
    | zero => rfl
    | succ n hm =>
      contradiction
  | succ n hn =>
    induction m with
    | zero =>
      contradiction
    | succ m _ =>
      simp [two, one, add] at h
      have hmn := hn m h
      rw [hmn]


end MyNats
