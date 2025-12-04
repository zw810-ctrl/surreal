import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.SetTheory.Game.Ordinal
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax

inductive Game where
  | mk : List Game → List Game → Game

open Game

def Game.left (g : Game) : List Game :=
  match g with
  | mk left _ => left

def Game.right (g : Game) : List Game :=
  match g with
  | mk _ right => right

def zero : Game := mk [] []
def minus_one : Game := mk [] [zero]
def one : Game := mk [zero] []
def half : Game := mk [zero] [one]


def Game.birthday (g : Game) : Nat :=
  match g with
  | mk L R =>
    let bL := L.map birthday
    let bR := R.map birthday
    (bL ++ bR).maximum.getD 0 + 1

#eval birthday zero
#eval birthday half -- 3

lemma list_maximum_is_none_then_is_empty (a : List ℕ) (non : a.maximum = none) : a = [] := by
  cases a with
  | nil => rfl
  | cons hd tl =>
    have ne_none : (hd :: tl).maximum ≠ none := by
      apply List.maximum_ne_bot_of_ne_nil
      simp
    contradiction

lemma elt_leq_max (a : List ℕ) (s : ℕ) (h : s ∈ a) : s ≤ a.maximum.getD 0 := by
    match max : a.maximum with
    | none =>
      have a_empty : a = [] := by
        apply list_maximum_is_none_then_is_empty a max
      rw [a_empty] at h
      contradiction
    | some m =>
      simp [max, Option.getD_some]
      exact List.le_of_mem_argmax h max


lemma birthday_lt_left (g : Game) (l : Game) (h : l ∈ g.left) :
    birthday l < birthday g := by
  cases g with
  | mk L R =>
    simp [left] at h
    simp [birthday]
    let b := List.map birthday L ++ List.map birthday R
    change birthday l < b.maximum.getD 0 + 1
    have h_mem_b : l.birthday ∈ b := by
      apply List.mem_append_left
      apply List.mem_map.mpr
      use l
    have a : l.birthday ≤ Option.getD b.maximum 0 := by
      apply elt_leq_max b l.birthday h_mem_b
    linarith

lemma birthday_lt_right (g : Game) (r : Game) (h : r ∈ g.right) :
    birthday r < birthday g := by
  cases g with
  | mk L R =>
    simp [right] at h
    simp [birthday]
    let b := List.map birthday L ++ List.map birthday R
    change birthday r < b.maximum.getD 0 + 1
    have h_mem_b : r.birthday ∈ b := by
      apply List.mem_append_right
      apply List.mem_map.mpr
      use r
    have aaa : r.birthday ≤ Option.getD b.maximum 0 := by
      apply elt_leq_max b r.birthday h_mem_b
    linarith

def Game.le (g h : Game) : Prop :=
    (∀ g_l ∈ g.left, ¬(le h g_l)) ∧ (∀ h_r ∈ h.right, ¬(le h_r g))
termination_by (birthday g + birthday h)
decreasing_by
  -- Prove termination for the first recursive call: `le h g_l`
  · have xl : g_l ∈ g.left := by assumption
    rw [add_comm h.birthday g_l.birthday]
    apply add_lt_add_right
    exact birthday_lt_left g g_l xl
  -- Prove termination for the second recursive call: `le h_r g`
  · have xr : h_r ∈ h.right := by assumption
    rw [add_comm h_r.birthday g.birthday]
    apply add_lt_add_left
    exact birthday_lt_right h h_r xr

theorem x_le_reprove : ∀ g h: Game, le g h ↔
  (∀ g_l ∈ g.left, ¬(le h g_l)) ∧ (∀ h_r ∈ h.right, ¬(le h_r g)) := by
  intro g h
  constructor
  · intro g_le_h
    unfold le at g_le_h
    apply And.intro
    · intro g_l hg_l
      exact g_le_h.1 g_l hg_l
    · intro h_r hh_r
      exact g_le_h.2 h_r hh_r
  · intro h_conds
    unfold le
    apply And.intro
    · intro g_l hg_l
      exact h_conds.1 g_l hg_l
    · intro h_r hh_r
      exact h_conds.2 h_r hh_r

theorem x_le_x : ∀ (x : Game), le x x := by
  let R : Game → Game → Prop := fun y x => birthday y < birthday x
  have wf_R : WellFounded R := InvImage.wf birthday wellFounded_lt

  intro x
  apply wf_R.induction x
  intro x IH
  unfold le
  unfold R at IH

  constructor
  . intro l xl
    intro h_contra
    unfold le at h_contra
    have h_neg_le := h_contra.1 l (by simp[xl, left]; exact xl)
    have h_le: le l l := IH l (birthday_lt_left x l xl)
    contradiction

  . intro r hr
    intro h_contra
    unfold le at h_contra
    have h_neg_le := h_contra.2 r (by simp[hr, right]; exact hr)
    have h_le: le r r := IH r (birthday_lt_right x r hr)
    contradiction

def Game.lt (g h : Game) : Prop := le g h ∧ ¬(le h g)

def Game.eq (g h : Game) : Prop :=
  le g h ∧ le h g


def IsSurreal (g : Game) : Prop :=
  (∀ g_l ∈ g.left, ∀ g_r ∈ g.right, ¬(le g_r g_l)) ∧
  (∀ g_l ∈ g.left, IsSurreal g_l) ∧
  (∀ g_r ∈ g.right, IsSurreal g_r)
termination_by g.birthday
decreasing_by
  · have xl : g_l ∈ g.left := by assumption
    exact birthday_lt_left g g_l xl
  · have xr : g_r ∈ g.right := by assumption
    exact birthday_lt_right g g_r xr

def Surreal := { g : Game // IsSurreal g }

-- To work with this, you can define helper functions.
instance : Coe Surreal Game where
  coe := Subtype.val

def Surreal.left (s : Surreal) : List Game := s.val.left
def Surreal.right (s : Surreal) : List Game := s.val.right

-- Example: Constructing surreal zero
-- We need to prove that the game `zero` has the property `IsSurreal`.
lemma isSurreal_zero : IsSurreal zero := by
  unfold IsSurreal
  constructor
  · -- The main condition
    simp [zero, Game.left, Game.right] -- The lists are empty, so it's true
  · -- The recursive conditions
    constructor
    · simp [zero, Game.left] -- The left list is empty
    · simp [zero, Game.right] -- The right list is empty

def surreal_zero' : Surreal := ⟨zero, isSurreal_zero⟩


def TripleNat := Nat × Nat × Nat
def myTuple : TripleNat := (10, 20, 5)
#eval myTuple.1 -- 10
#eval myTuple.2.1 -- 20
#eval myTuple.2.2 -- 5

structure Triple_Nat where
  a : Nat  -- The first natural number, named 'a'
  b : Nat  -- The second natural number, named 'b'
  c : Nat  -- The third natural number, named 'c'
deriving Repr -- This allows Lean to print instances of the type nicely

def myTriple : Triple_Nat := { a := 10, b := 24, c := 5 }
#eval myTriple.1  -- Output: 10 (the first element)
#eval myTriple.2  -- Output: 20 (the second element)
#eval myTriple.3  -- Output: 5  (the third element)

example (a b : Prop) (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b := by
  -- We have h : ¬(a ∧ b) in our local context.
  -- We want to transform it into h : ¬a ∨ ¬b.
  push_neg at h
  rw [imp_iff_not_or] at h
  -- The hypothesis h is now exactly our goal.
  exact h
