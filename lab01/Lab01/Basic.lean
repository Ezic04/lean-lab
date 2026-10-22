/- Lean course, lab scenario 01: Lean as a programming language -/

/- #eval shows the value of an expression; #check shows its type. -/
/- Observe the Lean InfoView (on the right).
   The output of these commands is visible in the "All messages" section. -/

#eval 2 + 2
#eval "Hello" ++ " " ++ "world"
#eval ["Hello"] ++ ["world"]

#check 2 + 2
#check "Hello" ++ " " ++ "world"
#check ["Hello"] ++ ["world"]

/- EXERCISE 1 -/
/- Try to concatenate a list of strings with a list of natural numbers.
   What does Lean say? -/

-- -- #check ["a"] ++ [1]

/- The type Nat represents natural numbers. -/

def square (x : Nat) : Nat := x * x

#check square
#eval square 5


/- EXERCISE 2 -/
/- Define pitagoras a b to return a^2 + b^2.
   Start by removing the sorry in the following definition.
   Remember `sorry` acts as a placeholder for "to be implemented".
-/

def pitagoras (a : Nat) (b : Nat) : Nat := a^2 + b^2

/- EXERCISE 3 -/
/- Read the output of #check below and interpret it.
   Then evaluate pit 1 using #eval. -/

def pit := pitagoras 7
#check  pit
#eval pit 1


/- EXERCISE 4 -/
/- Write a program similar to the one in the lecture, but with the following interaction: -/
/- Input the first number from one to four:
  Three
  Input the second number from one to four:
  Two
  The sum of your digits is five. -/
/- Use Nat to represent the numbers. -/
/- Try using do notation for Option. -/

syntax "[|" term term* "|]" : term
macro_rules
  | `([| $f $a |]) => `($f <$> $a)
  | `([| $f $as* $a |]) => `([| $f $as* |] <*> $a)

def parseNat4 (s : String) : Option Nat := s.toLower |> fun
  | "one" => some 1
  | "two" => some 2
  | "three" => some 3
  | "four" => some 4
  | _ => none

def toDigit : Nat → Option String
  | 0 => some "zero"
  | 1 => some "one"
  | 2 => some "two"
  | 3 => some "three"
  | 4 => some "four"
  | 5 => some "five"
  | 6 => some "six"
  | 7 => some "seven"
  | 8 => some "eight"
  | 9 => some "nine"
  | _ => none


def ofOption {m : Type → Type} [Monad m] {α : Type} (opt : Option α) : OptionT m α :=
  OptionT.mk (pure opt)

def askAndAdd : IO Unit := Functor.discard <| OptionT.run do
  let stdin ← .getStdin
  let getParsed := do
    let num_str ← stdin.getLine
    match parseNat4 num_str.trimAscii.toString with
      | some num => pure num
      | none => do
        IO.println "Failed to parse a number."
        ofOption none
  .println "Input the first number from one to four:"
  let first ← getParsed
  .println "Input the second number from one to four:"
  let second ← getParsed
  let some res := toDigit <| first + second
    | .println "Failed to generate text"
  .println s!"The sum of your digits is {res}."


/- EXERCISE 5 -/
/- Try removing the partial keyword in the following definition.
   Why does it fail?
   Fix this using pattern matching over n.
-/

def factorial : Nat → Nat
  | .zero => 1
  | .succ n => factorial n


/- EXERCISE 6 -/
/- Implement fib so that it returns the nth Fibonacci number. -/
def fib : Nat → Nat
 | 0 => 0
 | 1 => 1
 | n + 2 => fib n + fib (n + 1)

/- EXERCISE 7 -/
/- Implement the greatest common divisor function. -/
/- Does it need partial? -/
/- Implement a variant that uses fuel and does not need partial. -/

#eval 7 / 2
#eval 11 % 3

def gcdF (fuel : Nat) : Nat → Nat → Option Nat
  | a, 0 => some a
  | 0, b => some b
  | a, b => match fuel with
    | .succ f => gcdF f b (a.mod b)
    | .zero => none

def gcd : Nat → Nat → Option Nat := gcdF 1000

def gcdT (a b : Nat) (h : a > b) : Nat :=
  match a, b with
  | a, 0 => a
  | a, b@(k + 1) =>
    have hb : 0 < b := by omega
    let h' : a % b < b := Nat.mod_lt a hb
    gcdT b (a % b) h'


/- EXERCISE 8 (Optional) -/
/- Think of a few other examples of functions on natural numbers or lists
   which are hard to implement in a way
   that makes it clear to Lean that they terminate.
   Implement one of them using the partial keyword, then using fuel. -/

def collatz (n : Nat) : Nat :=
  if h : 2 ∣ n then n.divExact 2 h else 3 * n + 1

theorem collatz_ne_zero (n : Nat) [hz : NeZero n] : collatz n ≠ 0 := by
  rw [collatz]
  by_cases h_dvd : 2 ∣ n
  · simp [h_dvd]
    have : n ≠ 1 := by
      intro hn
      simp [hn] at h_dvd
    have := hz.ne
    omega
  · simp [h_dvd]

partial def iterCollatz (n : Nat) [NeZero n] : Nat :=
  if n == 1 then 0 else 1 + @iterCollatz (collatz n) (NeZero.mk <| collatz_ne_zero n)

#eval iterCollatz 27

/- EXERCISE 9
   Write functions sumL and squareL that, given a list of natural numbers,
   return their sum or the list of their squares, respectively.
   Do this in two ways:
   1. Recursive definitions
   2. Using functions List.map and List.foldr.
   -/

def sumL : List Nat → Option Nat
  | [] => none
  | [x] => x
  | x :: xs => match sumL xs with
    | none => none
    | some acc => x + acc

def squareL : List Nat → List Nat
  | [] => []
  | x :: xs => x^2 :: squareL xs

def sumL2 (l : List Nat) : Option Nat :=
  l.foldl (fun acc x => acc.map (· + x)) none

def squareL2 (l : List Nat) : List Nat := l.map (·^2)

/- EXERCISE 10
   Implement addition and multiplication for the following simple representation of complex numbers. -/
structure MyCmplx where
  re : Int
  im: Int

def add (x y : MyCmplx) : MyCmplx := ⟨x.re + y.re, x.im + y.im⟩
def mul (x y : MyCmplx) : MyCmplx := ⟨x.re * y.re, x.im * y.im⟩

/- EXERCISE 11 -/
/- Implement an Ord instance for MyCmplx: compare re^2 + im^2 first,
   then re, then im to break ties. -/

instance : Ord MyCmplx where
  compare x y := if x.re ≠ y.re then compare x.re y.re else compare x.im y.im

/- EXERCISE 12 (Optional) -/
/- Remove deriving Repr from the definition of MyCmplx and implement
   a custom instance that formats the complex number as "a+bi". -/

instance : Repr MyCmplx where
  reprPrec c p := s!"{reprPrec c.re p}+{reprPrec c.im p}i"

/- EXERCISE 13 (Optional) -/
/- Implement a simple incremental dictionary on Int using binary search trees (BSTs). -/

inductive BST where
 | leaf
 | node (x : Int) (left : BST) (right : BST)

-- Check if x is present in t
def BST.find : BST → Int → Bool
  | leaf, _ => false
  | node y l r, x => match (compare y x) with
    | .eq => true
    | .lt => l.find x
    | .gt => r.find x

-- Add x to t if it is not there yet
def BST.add : BST → Int → BST
  | leaf, _ => leaf
  | n@(node y l r), x => match (compare y x) with
    | .eq => n
    | .lt => l.add x
    | .gt => r.add x


-- Return the number of elements in BST
def BST.size : BST → Nat
  | leaf => 1
  | node _ l r => l.size + 1 + r.size

/- Tests for your BST implementation -/
def test_BST (t : BST) (expected_size : Nat) (test_list : List Int) (expected_ans : List Bool) : List String :=
  [ if BST.size t == expected_size then "Size OK" else "Size ERR",
    if List.map (BST.find t) test_list == expected_ans then "Tests OK" else "Tests ERR"]

def BST_test_list : List Int := [0, 1, 3, 8, 4, 0, -1]

def t1 := BST.leaf
-- #eval test_BST t1 0 BST_test_list [false, false, false, false, false, false, false]

def t2 := List.foldl BST.add t1 [1, 1, 5, 3, 8, 2, 8]
-- #eval test_BST t2 5 BST_test_list [false, true, true, true, false, false, false]

def t3 := List.foldl BST.add t2 [-1, -3, 8, 4]
-- #eval test_BST t3 8 BST_test_list [false, true, true, true, true, false, true]
