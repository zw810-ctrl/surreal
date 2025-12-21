import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Surreal.game
import Surreal.surreal

-- We wish to define addition on surreal numbers. But first we need
-- to define addition on games.
def Game.add : Game → Game → Game
  | x, y =>
    let L := (x.left.map (fun xl => Game.add xl y)) ++ (y.left.map (fun yl => Game.add x yl))
    let R := (x.right.map (fun xr => Game.add xr y)) ++ (y.right.map (fun yr => Game.add x yr))
    Game.mk L R
  termination_by x y => x.birthday + y.birthday
  decreasing_by
    · sorry
    · sorry
    · sorry
    · sorry
