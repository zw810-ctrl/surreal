import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Surreal.game
import Surreal.surreal

-- We wish to define addition on surreal numbers. But first we need
-- to define addition on games.
open Game
def Game.add : Game → Game → Game
  | x, y =>
    match hx : x, hy : y with
    | mk XL XR, mk YL YR =>
      let L := (XL.map (fun xl => xl.add y)) ++ (YL.map (fun yl => x.add yl))
      let R := (XR.map (fun xr => xr.add y)) ++ (YR.map (fun yr => x.add yr))
      mk L R
  termination_by x y => x.birthday + y.birthday
  decreasing_by
    · sorry
    · sorry
    · sorry
    · sorry




theorem Game.add_zero (a : Game) : Game.add a zero = a := by
  sorry

theorem Game.zero_add (a : Game) : Game.add zero a = a := by
  sorry


-- These two lemmas must be proved hand-in-hand by induction on
-- birthday(a) + birthday(b) + birthday(a') + birthday(b').
-- Perhaps need to group them into one theorem using `and`.
lemma Game.Addlem1 (a b a' b' : Game) :
  (a.le a) ∧ (b.le b) → (a.add b).le (a'.add b') := by
  sorry

lemma Game.Addlem2  (a b a' b' : Game) :
  (a'.add b').le (a.add b) ∧ (b.le b') → (a'.le a) := by
  sorry


theorem Game.add_equal (a b a' b' : Game) :
  (a.eq a') ∧ (b.eq b') → (a.add b).eq (a'.add b') := by
  sorry

theorem Game.add_lt (a b a' b' : Game) :
  (a.lt a') ∧ (b.le b') → (a.add b).lt (a'.add b') := by
  sorry

-- addition is commutative: check whether one needs a, b to be surreal
theorem Game.add_comm (a b : Game) :
  a.add b = b.add a := by
  sorry

theorem Game.add_assoc (a b c : Game) :
  (a.add b).add c = a.add (b.add c) := by
  sorry

def Game.neg : Game → Game
  | g =>
    let L := g.right.map (fun r => Game.neg r)
    let R := g.left.map (fun l => Game.neg l)
    Game.mk L R
  termination_by g => g.birthday
  decreasing_by
    · sorry
    · sorry

theorem Game.add_neg (a : Game) :
  (a.add (Game.neg a)).eq zero := by
  sorry

theorem Game.neg_add (a : Game) :
  ((Game.neg a).add a).eq zero := by
  sorry

theorem Game.neg_isSurreal (a : Surreal) :
  IsSurreal (Game.neg a) := by
  sorry

theorem Game.add_isSurreal (a b : Surreal) :
  IsSurreal (a.val.add b.val) := by
  sorry



def Game.mult : Game → Game → Game
  | x, y =>
  match hx : x, hy : y with
  | mk XL XR, mk YL YR =>
    let L :=
      List.zipWith (fun xl yl => ((xl.mult y).add (x.mult yl)).add (xl.mult yl).neg) XL YL ++
      List.zipWith (fun xr yr => ((xr.mult y).add (x.mult yr)).add (xr.mult yr).neg) XR YR
    let R :=
      List.zipWith (fun xl yr => ((xl.mult y).add (x.mult yr)).add (xl.mult yr).neg) XL YR ++
      List.zipWith (fun xr yl => ((xr.mult y).add (x.mult yl)).add (xr.mult yl).neg) XR YL
  Game.mk L R
  termination_by x y => x.birthday + y.birthday
  decreasing_by
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
