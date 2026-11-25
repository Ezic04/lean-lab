/- Lean course, lab scenario 08 -/

/- EXERCISE 1
   Today, we work with binary trees.
   Below is a simple tree with an Int value.
   Furthermore, we define a mirror operation.
   Prove that the mirror operation is an involution.
-/
inductive Tree where
 | leaf
 | node (x : Int) (left : Tree) (right : Tree)

@[simp] def Tree.mirror : Tree → Tree
  | leaf           => leaf
  | node x left right     => node x (mirror right) (mirror left)

theorem Tree.mirror_involutive (t : Tree) : t.mirror.mirror = t := by
  induction t with
  | leaf => rfl
  | node x l r hl hr => simp [hl, hr]

 /- EXERCISE 2
    Prove the following two helper functions.
    Then, express a property that a tree is a BST. (Hint: Tree.All may be useful.)
 -/

-- True if all values of t satisfy p
def Tree.All (p : Int → Prop) : Tree → Prop
  | leaf => True
  | node x l r => p x ∧ All p l ∧ All p r

--- True if there exists a value in t that satisfies p
def Tree.Exists (p : Int → Prop) : Tree → Prop
  | leaf => False
  | node x l r => p x ∨ Exists p l ∨ Exists p r

-- True if t is a BST
def Tree.IsBST : Tree → Prop
  | leaf => True
  | node x l r => (All (· < x) l ∧ IsBST l) ∧ (All (x < ·) r ∧ IsBST r)

theorem Tree.IsBST.left (h : (Tree.node x l r).IsBST) : l.IsBST := h.1.2

theorem Tree.IsBST.right (h : (Tree.node x l r).IsBST) : r.IsBST := h.2.2

/- We define a BST as a subtype of Tree.
   Given bst : BST, you can have bst.value : Tree or bst.property : Prop to access the value and
   the proof of the property, respectively.
   It may also be useful to write statements like let ⟨ t, h ⟩ := bst to unpack a bst : BST.
-/
abbrev BST := { t : Tree // t.IsBST }

/- EXERCISE 3
   Write a find function for a BST and a proof that it is correct.
   Hints:
    - In the function definition, for recursion you'll need to supply proofs that the left/right trees are BSTs.
      The following notation may be useful: if h : p ∧ q, then h.1 and h.2 correspond to p and q, respectively.
    - Our solution uses a lot of simp and simpa to clear out mess.
    - induction _ generalizing _ may be a useful construction.
-/
def BST_find (bst : BST) (x : Int) : Bool :=
  match bst with
  | ⟨.leaf, _⟩ => false
  | ⟨.node y l r, h⟩ => x == y || BST_find ⟨l, h.left⟩ x || BST_find ⟨r, h.right⟩ x


theorem bst_find_correct :
  ∀ bst : BST, ∀ x : Int, Tree.Exists (· == x) bst ↔ BST_find bst x == True
  := by
  intro ⟨t, h⟩ x
  constructor
  · intro he
    -- match bst with
    induction t with
    | leaf =>
      trivial
    | node y l r hl hr =>
      rw [Tree.Exists] at he
      rw [BST_find]
      by_cases (x == y)
      case neg h_ne =>
        sorry
      case pos h_eq => sorry
    -- | ⟨.node y l r, h⟩ =>
      -- rw [Tree.Exists] at he

  · sorry

/- EXERCISE 4
   Define addition to a BST: BST_add.
   The difficulty here is to prove that the resulting tree is still a BST.
   This is not just a simple juggle of the output of the recursion, there will be a helper theorem
   needed to prove a bit more about addition to subtrees.
   (Warning: this is quite a substantial exercise, our solution has around 30 lines with some helper theorems.)
   Hint: we found `split` a useful tactic here. `split` breaks match / if-then-else
         statements into cases.
-/

def BST_add (bst : BST) (x : Int) : BST := sorry

/- EXERCISE 5
   Prove that after addition, the tree contains the element.
   Hint: here, you may actually want to *forget* that this is a BST.
         `clear h` removes a hypothesis h from a context.
         This may be useful before calling `induction`, so that you
         do not need to prove something useless in the inductive step.
-/
theorem bst_add_correct : ∀ bst : BST, ∀ x : Int, Tree.Exists (fun y => x == y) (BST_add bst x) := sorry
