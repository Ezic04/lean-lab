/- Lean course, lab scenario 02: dependent type theory (student skeleton) -/

/- EXERCISE 0: definitions from the lecture
   Go through Vec, Matrix, append, rep, appendCol, and transpose below.
   Make sure you understand their types and each pattern-matching branch.
-/

/- A brief reminder:
   Vec a n contains n elements; Matrix a n m contains n rows of m elements.
   Remember: Nat is inductively defined by `zero : Nat` and `succ : Nat → Nat`.
   The constructors are usually denoted by `0` and `n + 1`.
   Nat addition recurses on its second argument:
     `n + 0 = n`
     `n + Nat.succ m = Nat.succ (n + m)`
   These equations hold "by definition".
   In contrast, `0 + n = n` and `(n + 1) + m = (n + m) + 1`
   do not hold "by definition" and are not automatically
   accepted by the type checker.
-/

inductive Vec (a : Type u) : Nat → Type (u + 1) where
  | nil : Vec a 0
  | cons {m : Nat} : a → Vec a m → Vec a (m + 1)
deriving Repr

namespace Vec

abbrev Matrix a n m := Vec (Vec a m) n

def append (v₁ : Vec a n) (v₂ : Vec a m) : Vec a (m + n) :=
  match v₁ with
  | nil => v₂
  | cons x xs => cons x (append xs v₂)

def rep (elem : a) (n : Nat) : Vec a n :=
  match n with
  | 0 => nil
  | n' + 1 => cons elem (rep elem n')

def appendCol (elems : Vec a x) (matrix : Matrix a x y) : Matrix a x (y + 1) :=
  match elems, matrix with
  | nil, nil => nil
  | cons e elems', cons row rows =>
    cons (cons e row) (appendCol elems' rows)

def transpose (matrix : Matrix a h w) : Matrix a w h :=
  match matrix with
  | nil => rep nil w
  | cons row rows => appendCol row (transpose rows)

/- EXERCISE 1: Implement the vector version of the map function, which
   applies f to every element of a vector, preserving its length. -/
def map (f : a → b) : Vec a n → Vec b n
  | nil => .nil
  | cons x xs => .cons (f x) (map f xs)

abbrev Vect := flip Vec

-- Uncomment after implementing:
#eval map (fun x : Int => x + 10) (cons 1 (cons 2 nil))
-- Expected: cons 11 (cons 12 nil)

def foldl : Vec α n → (α → β → β) → β → β
  | nil, _, b => b
  | cons a as, f, acc => f a (as.foldl f (f a acc))

def foldr : Vec α n → (α → β → β) → β → β
  | nil, _, b => b
  | cons a as, f, acc => as.foldr f (f a acc)

instance : Singleton α (Vec α 1) where
  singleton x := .cons x .nil

instance : Functor (Vect n) where
  map := map

instance : Pure (Vect n) where
   pure a := rep a n

def Vec.seq {α β : Type u} {n : Nat} : Vec (α → β) n → (Unit → Vec α n) → Vec β n
  | nil, _ => .nil
  | cons f fs, as' =>
    match as' () with
    | .cons a as => .cons (f a) (Vec.seq fs (fun _ => as))

instance : Seq (Vect n) where
  seq := Vec.seq

instance : Applicative (Vect n) where

syntax "[|" term term* "|]" : term
macro_rules
  | `([| $f $a |]) => `($f <$> $a)
  | `([| $f $as* $a |]) => `([| $f $as* |] <*> $a)


/- EXERCISE 2: scalar product over Int
   Implement the scalar product: multiply corresponding elements and add the results.
   The scalar product of empty vectors is 0. -/
def scalarProduct (v₁ v₂ : Vect n Int) : Int :=
  [| Int.mul v₁ v₂ |].foldr Int.add 0

/- EXERCISE 3: reverse
   Write BOTH the type and implementation of a function that reverses a vector.
   Its type should express that reversing preserves the length.
   HINT: If using append does not work, try implementing a `snoc` helper function
   that adds an element to the end of a vector.
-/
def reverse : Vect n α → Vect n α
  | nil => nil
  | cons (m := m) x xs => Nat.add_comm 1 m ▸ append (reverse xs) {x}

-- Uncomment after implementing:
#eval reverse (cons 1 (cons 2 (cons 3 nil)))
-- Expected: cons 3 (cons 2 (cons 1 nil))

/- EXERCISE 4: matrix multiplication over Int
   Write BOTH the type and implementation of matrixMultiplication.
   If the first matrix has n rows and k columns, what dimensions must
   the second matrix have, and what dimensions will the result have?
   HINT: You can reuse the vector functions defined above.
-/
-- def matrixMultiplication : Matrix Int m n → Matrix Int m n → Matrix Int m k
def matrixMultiplication (a : Matrix Int m n) (b : Matrix Int n k) : Matrix Int m k :=
  let b' := transpose b
  a.map (fun a => b'.map (scalarProduct a))


-- Tests for matrix multiplication: uncomment after implementing.
def testMatrixA : Matrix Int 2 3 :=
  cons (cons 1 (cons 2 (cons 3 nil)))
    (cons (cons 4 (cons 5 (cons 6 nil))) nil)
def testMatrixB : Matrix Int 3 2 :=
  cons (cons 7 (cons 8 nil))
    (cons (cons 9 (cons 10 nil))
      (cons (cons 11 (cons 12 nil)) nil))
#eval matrixMultiplication testMatrixA testMatrixB
-- Expected: [[58, 64], [139, 154]], represented using cons and nil.

/- EXERCISE 5: finite indices
   In namespace Vec, define your own inductive type Fin k representing natural
   numbers strictly smaller than k. Use zero and successor constructors.
   Observe that `Fin 0` has no elements.
   (Remember, we are still in the namespace Vec. Lean has a predefined type Fin k.)
 -/

inductive Fin : Nat → Type where
  | zero : Fin (n + 1)
  | succ (i : Fin n) : Fin (n + 1)

-- After defining your own Fin above, uncomment and implement:

def getElem : Fin k → Vec a k → a
  | Fin.zero, cons x _ => x
  | Fin.succ i, cons _ xs => xs.getElem i

#eval getElem Fin.zero (cons 10 (cons 20 (cons 30 nil))) -- 10
#eval getElem (Fin.succ Fin.zero) (cons 10 (cons 20 (cons 30 nil))) -- 20

end Vec

structure SelfOrSucc (n : Nat) (α : Nat → Type) where
  rest : Fin 2
  val : α (n + rest)

namespace SelfOrSucc

def mkSelf (a : α n) : SelfOrSucc n α := ⟨0, a⟩
def mkSucc (a : α (n + 1)) : SelfOrSucc n α := ⟨1, a⟩

def isSucc  (x : SelfOrSucc n α) : Bool := x.rest == 1

-- theorem succ_res_one (x : SelfOrSucc n α) (h : x.isSucc = true) : x.rest.toNat = 1 := eq_of_beq h

theorem succ_res_one (x : SelfOrSucc n α) (h : x.isSucc = b) : x.rest.toNat = b.toNat := by
  rw [isSucc] at h
  cases b
  · simp
  -- · simp [ne_of_beq_false h]
    sorry
  · simp [eq_of_beq h]



-- def NumOrSucc.map_inc (x : SelfOrSucc n α) (f : ∀ {m}, α m → α (m + 1)) : SelfOrSucc (n + 1) α :=
--   NumOrSucc.mk x.is_succ (Nat.add_right_comm n x.is_succ.toNat 1 ▸ f x.val)
-- abbrev mkGrow (t : α (n + 1)) : SelfOrSucc n α := NumOrSucc.mk 1 t
-- abbrev mkSame (t : α n) : SelfOrSucc n α := NumOrSucc.mk 0 t

end SelfOrSucc

/- EXERCISE 6: AVL insertion
   Constructors enforce height balance, but do not enforce search order.
   Implement the easy part of insert that does not require rotations.
   Use compare to preserve search order for an input search tree, and leave
   equal elements unchanged. Identify the hard cases that require rotations
   and leave those branches as sorry. -/
inductive AVL (α : Type) : Nat → Type where
  | empty : AVL α 0
  | balanced (elem : α) (l : AVL α h) (r : AVL α h) : AVL α (h + 1)
  | leftHeavy (elem : α) (l : AVL α (h + 1)) (r : AVL α h) : AVL α (h + 2)
  | rightHeavy (elem : α) (l : AVL α h) (r : AVL α (h + 1)) : AVL α (h + 2)

namespace AVL

-- inductive InsertResult (a : Type) (n : Nat) : Type where
--   | sameHeight : AVL a n → InsertResult a n
--   | increasedHeight : AVL a (n + 1) → InsertResult a n


def insert [Ord α] (t : AVL α h) (x : α) : SelfOrSucc h (AVL α) :=
  match t with
  | empty => .mkSucc (balanced x empty empty)
  | t@(balanced e l r) =>
    match compare x e with
    | .eq => .mkSelf t
    | .lt =>
      let lu := insert l x
      if h : lu.isSucc then
        let lh := leftHeavy e (SelfOrSucc.succ_res_one lu h ▸ lu.val) r
        sorry
      else balanced e lu.val r
    | .gt => sorry
  | t@(leftHeavy e l r) =>
    let lc := .mkSelf t
    let rc := .mkSelf t
    match_ord e t lc rc
  | t@(rightHeavy e l r) =>
    let lc := .mkSelf t
    let rc := .mkSelf t
    match_ord e t lc rc
  match_ord {k} (e : a) (t : AVL a k) (lc rc : SelfOrSucc k (AVL a)) : SelfOrSucc k (AVL a) :=
    match compare x e with
    | .eq => .mkSelf t
    | .lt => lc
    | .gt => rc

/- EXERCISE 7 (*) (optional): AVL rotations
   Extend your implementation of insert by implementing the rotation parts
   as well (at least one of them). You can find resources about AVL online.
-/

end AVL
