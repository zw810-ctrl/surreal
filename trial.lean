import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Surreal.game
import Surreal.surreal
import Surreal.addition


--- This is not used in the main theorems we are going to prove. ----
instance : LawfulBEq Game where
  eq_of_beq := by sorry
  rfl := by sorry


#eval [zero, one].erase one
#eval [zero, one].erase half


def Game.remove_left (g : Game) (l : Game) : Game :=
  mk ((g.left).erase l) g.right

def Game.remove_right (g : Game) (r : Game) : Game :=
  mk g.left (g.right.erase r)

#eval half
#eval half.remove_right one
#eval half.remove_left zero

lemma remove_left_eq_right (g : Game) (l : Game) :
  (g.remove_left l).right = g.right := by
  simp [Game.remove_left]
  simp [Game.right]

lemma remove_left_subset_left (g : Game) (l : Game) :
  (g.remove_left l).left ⊆ g.left := by
  simp [Game.remove_left, Game.left]
  apply List.erase_subset

lemma remove_left_contains_all_but (g l x : Game) (hx : x ∈ g.left) (h_neq : x ≠ l) :
  x ∈ (g.remove_left l).left := by
  change x ∈ g.left.erase l
  simp [List.mem_erase_of_ne, h_neq]
  exact hx

lemma remove_left_dom_remains (g l l' : Game) (hl' : l' ∈ g.left) (h_dom : l.lt l') :
  l' ∈ (g.remove_left l).left := by
  have h_neq : l' ≠ l := by
    by_contra h_eq
    have h : l'.le l := by rw[h_eq]; exact Game.le_congr
    have h_contra := h_dom.2
    contradiction
  apply remove_left_contains_all_but g l l' hl' h_neq

lemma remove_right_eq_left (g : Game) (r : Game) :
  (g.remove_right r).left = g.left := by
  simp [Game.remove_right]
  simp [Game.left]

lemma remove_right_subset_right (g : Game) (r : Game) :
  (g.remove_right r).right ⊆ g.right := by
  simp [Game.right]
  apply List.erase_subset

lemma remove_right_contains_all_but (g x r : Game) (hx : x ∈ g.right) (h_neq : x ≠ r) :
  x ∈ (g.remove_right r).right := by
  change x ∈ g.right.erase r
  simp [List.mem_erase_of_ne, h_neq]
  exact hx

lemma remove_right_dom_remains (g r' r : Game) (hr' : r' ∈ g.right) (h_dom : r'.lt r) :
  r' ∈ (g.remove_right r).right := by
  have h_neq : r' ≠ r := by
    by_contra h_eq
    have h : r.le r' := by rw[h_eq]; exact Game.le_congr
    have h_contra := h_dom.2
    contradiction
  apply remove_right_contains_all_but g r' r hr' h_neq



theorem left_removal_IsSurreal
    (x : Surreal) (l : Game) : IsSurreal (x.val.remove_left l) := by
    have h1 : (x.val.remove_left l).left ⊆ x.left := remove_left_subset_left x.val l
    have h2 : (x.val.remove_left l).right = x.right := remove_left_eq_right x.val l
    unfold IsSurreal
    constructor
    · intro yl h_yl yr h_yr
      apply h1 at h_yl
      rw [h2] at h_yr
      have h_surreal := (x.property)
      unfold IsSurreal at h_surreal
      exact h_surreal.1 yl h_yl yr h_yr
    · constructor
      · intro xl h_xl
        apply h1 at h_xl
        have h_surreal := (x.property)
        unfold IsSurreal at h_surreal
        exact h_surreal.2.1 xl h_xl
      · intro xr h_xr
        rw [h2] at h_xr
        have h_surreal := (x.property)
        unfold IsSurreal at h_surreal
        exact h_surreal.2.2 xr h_xr

theorem right_removal_IsSurreal
    (x : Surreal) (r : Game) : IsSurreal (x.val.remove_right r) := by
    have h1 : (x.val.remove_right r).left = x.left := by rfl
    have h2 : (x.val.remove_right r).right ⊆ x.right := remove_right_subset_right x.val r
    unfold IsSurreal
    constructor
    · intro yl h_yl yr h_yr
      rw [h1] at h_yl
      apply h2 at h_yr
      have h_surreal := (x.property)
      unfold IsSurreal at h_surreal
      exact h_surreal.1 yl h_yl yr h_yr
    · constructor
      · intro xl h_xl
        rw [h1] at h_xl
        have h_surreal := (x.property)
        unfold IsSurreal at h_surreal
        exact h_surreal.2.1 xl h_xl
      · intro xr h_xr
        apply h2 at h_xr
        have h_surreal := (x.property)
        unfold IsSurreal at h_surreal
        exact h_surreal.2.2 xr h_xr

lemma like_le (x y : Surreal) :
  (∀ xl ∈ x.left, ∃ yl ∈ y.left, xl.le yl) ∧
  (∀ yr ∈ y.right, ∃ xr ∈ x.right, xr.le yr) → x.le y := by
  intro h
  unfold Surreal.le
  unfold Game.le
  constructor
  · intro xl h_xl
    by_contra h_le
    have h1 := h.1 xl h_xl
    rcases h1 with ⟨yl, h_yl, xl_le_yl⟩
    have y_le_yl := Game.le_trans ⟨h_le, xl_le_yl⟩
    have y_nleq_yl := ((xL_x_xR y).1 yl h_yl).2
    contradiction
  · intro yr h_yr
    by_contra h_le
    have h2 := h.2 yr h_yr
    rcases h2 with ⟨xr, h_xr, xr_le_yr⟩
    have xr_le_x := Game.le_trans ⟨xr_le_yr, h_le⟩
    have xr_nleq_x := ((xL_x_xR x).2 xr h_xr).2
    contradiction

-- The theorem below uses lawfulBEq on Game.eq
theorem simplicity_left (x : Surreal) (l l' : Game)
  (hl' : l' ∈ x.left) (h_dom : l.lt l') : (x.val.remove_left l).eq x := by
  unfold Game.eq
  let y : Surreal := ⟨x.val.remove_left l, left_removal_IsSurreal x l⟩
  constructor
  -- Prove `(x.remove_left l) ≤ x` by like_le
  · apply like_le y x
    constructor
    · intro yl h_yl
      use yl
      constructor
      · have h1 : (x.val.remove_left l).left ⊆ x.left := remove_left_subset_left x.val l
        have h2 : (x.val.remove_left l).left = y.left := by rfl
        rw [h2] at h1
        apply h1 at h_yl
        exact h_yl
      · exact Game.le_congr
    · intro xr h_xr
      use xr
      constructor
      · have h1 : (x.val.remove_left l).right = x.right := remove_left_eq_right x.val l
        have h2: y.right = (x.val.remove_left l).right := by rfl
        rw [h2]
        exact h_xr
      · exact Game.le_congr
  -- Prove `x ≤ (x.remove_left l)` by like_le
  · apply like_le x y
    constructor
    · intro xl h_xl
      by_cases h_case : xl = l
      · -- case: xl = l, take yl = l'
        rw [h_case]
        use l'
        constructor
        · have h : l' ∈ (x.val.remove_left l).left :=
          remove_left_dom_remains x.val l l' hl' h_dom
          exact h
        · exact h_dom.1
      · -- case: xl ≠ l, take yl = xl
        use xl
        constructor
        · have h : xl ∈ (x.val.remove_left l).left :=
          remove_left_contains_all_but x.val l xl h_xl h_case
          exact h
        · exact Game.le_congr
    · intro yr h_yr
      use yr
      constructor
      · have h1 : (x.val.remove_left l).right = x.right := remove_left_eq_right x.val l
        have h2: y.right = (x.val.remove_left l).right := by rfl
        rw [h2] at h_yr
        exact h_yr
      · exact Game.le_congr

theorem simplicity_right (x : Surreal) (r r' : Game)
  (hr' : r' ∈ x.right) (h_dom : r'.lt r) : (x.val.remove_right r).eq x := by
  unfold Game.eq
  let y : Surreal := ⟨x.val.remove_right r, right_removal_IsSurreal x r⟩
  constructor
  -- Prove `(x.remove_right r) ≤ x` by like_le
  · apply like_le y x
    constructor
    · intro yl h_yl
      use yl
      constructor
      · have h1 : (x.val.remove_right r).left = x.left := by rfl
        have h2 : (x.val.remove_right r).left = y.left := by rfl
        rw [h2] at h1
        rw [h1.symm]
        exact h_yl
      · exact Game.le_congr
    · intro xr h_xr
      by_cases h_case : xr = r
      · -- case: xr = r, take yr = r'
        rw [h_case]
        use r'
        constructor
        · have h : r' ∈ (x.val.remove_right r).right :=
          remove_right_dom_remains x r' r hr' h_dom
          exact h
        · exact h_dom.1
      · -- case: xr ≠ r, take yr = xr
        use xr
        constructor
        · have h : xr ∈ (x.val.remove_right r).right :=
          remove_right_contains_all_but x.val xr r h_xr h_case
          exact h
        · exact Game.le_congr

  -- Prove `x ≤ (x.remove_right r)` by like_le
  · apply like_le x y
    constructor
    · intro xl h_xl
      use xl
      constructor
      · have h1 : (x.val.remove_right r).left = x.left := by rfl
        have h2: y.left = (x.val.remove_right r).left := by rfl
        rw [h2]
        exact h_xl
      · exact Game.le_congr
    · intro yr h_yr
      use yr
      constructor
      · have h1 : (x.val.remove_right r).right ⊆ x.right := remove_right_subset_right x.val r
        have h2 : (x.val.remove_right r).right = y.right := by rfl
        rw [h2] at h1
        apply h1 at h_yr
        exact h_yr
      · exact Game.le_congr
