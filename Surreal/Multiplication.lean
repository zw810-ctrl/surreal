import Mathlib.Tactic.Linarith
import Mathlib.Data.List.MinMax
import Mathlib.Order.Basic
import Surreal.game
import Surreal.surreal
import Surreal.addition

-------------------------------------------
---------- Definition of a*b --------------
-------------------------------------------
def flatten {α : Type} : List (List α) → List α
  | [] => []
  | (x :: xs) => x ++ flatten xs


def Game.mul : Game → Game → Game
  | x, y =>
  match _hx : x, _hy : y with
  | mk XL XR, mk YL YR =>
    let L :=
      flatten (XL.attach.map (fun lx =>
        let xl := lx.val
        let _hxl := lx.property
        YL.attach.map (fun ly =>
          let yl := ly.val
          let _hyl := ly.property
          ((xl.mul y).add (x.mul yl)).add (xl.mul yl).neg
        )
      )) ++
      flatten (XR.attach.map (fun rx =>
        let xr := rx.val
        let _hxr := rx.property
        YR.attach.map (fun ry =>
          let yr := ry.val
          let _hyr := ry.property
          ((xr.mul y).add (x.mul yr)).add (xr.mul yr).neg
        )
      ))

    let R :=
      flatten (XL.attach.map (fun lx =>
        let xl := lx.val
        let _hxl := lx.property
        YR.attach.map (fun ry =>
          let yr := ry.val
          let _hyr := ry.property
          ((xl.mul y).add (x.mul yr)).add (xl.mul yr).neg
        )
      )) ++
      flatten (XR.attach.map (fun rx =>
        let xr := rx.val
        let _hxr := rx.property
        YL.attach.map (fun ly =>
          let yl := ly.val
          let _hyl := ly.property
          ((xr.mul y).add (x.mul yl)).add (xr.mul yl).neg
        )
      ))
    Game.mk L R
  termination_by x y => Game.birthday x + Game.birthday y
  decreasing_by
  -- 1. xl * y
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hxl)
    have hmeasure : xl.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxl_lt y.birthday
    simpa [_hy] using hmeasure

  -- 2. x * yl
  · have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hyl)
    have hmeasure : x.birthday + yl.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyl_lt x.birthday
    simpa [_hx] using hmeasure

  -- 3. xl * yl
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hxl)
    have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hyl)
    have hmeasure : xl.birthday + yl.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxl_lt hyl_lt
    assumption

  -- 4. xr * y
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (by simpa [Game.right] using _hxr)
    have hmeasure : xr.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxr_lt y.birthday
    simpa [_hy] using hmeasure

  -- 5. x * yr
  · have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right (by simpa [Game.right] using _hyr)
    have hmeasure : x.birthday + yr.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyr_lt x.birthday
    simpa [_hx] using hmeasure

  -- 6. xr * yr
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (by simpa [Game.right] using _hxr)
    have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right  (by simpa [Game.right] using _hyr)
    have hmeasure : xr.birthday + yr.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxr_lt hyr_lt
    assumption

  -- 7. xl * y
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hxl)
    have hmeasure : xl.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxl_lt y.birthday
    simpa [_hy] using hmeasure

  -- 8. x * yr
  · have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right (by simpa [Game.right] using _hyr)
    have hmeasure : x.birthday + yr.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyr_lt x.birthday
    simpa [_hx] using hmeasure

  -- 9. xl * yr
  · have hxl_lt : xl.birthday < (mk XL XR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hxl)
    have hyr_lt : yr.birthday < (mk YL YR).birthday :=
      birthday_lt_right  (by simpa [Game.right] using _hyr)
    have hmeasure : xl.birthday + yr.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxl_lt hyr_lt
    assumption

  -- 10. xr * y
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (by simpa [Game.right] using _hxr)
    have hmeasure : xr.birthday + y.birthday < (mk XL XR).birthday + y.birthday :=
      add_lt_add_right hxr_lt y.birthday
    simpa [_hy] using hmeasure

  -- 11. x * yl
  · have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hyl)
    have hmeasure : x.birthday + yl.birthday < x.birthday + (mk YL YR).birthday :=
      add_lt_add_left hyl_lt x.birthday
    simpa [_hx] using hmeasure

  -- 12. xr * yl
  · have hxr_lt : xr.birthday < (mk XL XR).birthday :=
      birthday_lt_right (by simpa [Game.right] using _hxr)
    have hyl_lt : yl.birthday < (mk YL YR).birthday :=
      birthday_lt_left (by simpa [Game.left] using _hyl)
    have hmeasure : xr.birthday + yl.birthday < (mk XL XR).birthday + (mk YL YR).birthday :=
      add_lt_add hxr_lt hyl_lt
    assumption

-------------------------------------------
--------------- a*0 = 0 -------------------
-------------------------------------------

lemma flatten_replicate_nil {α} (n : Nat) : flatten (List.replicate n ([] : List α)) = [] := by
  induction n with
  | zero =>
    simp [List.replicate, flatten]
  | succ n ih =>
    simp [List.replicate, flatten, ih]

theorem Game.mul_zero (a : Game) : Game.mul a zero = zero := by
  apply wf_R.induction a
  intro x IH
  rw [zero]
  unfold mul
  match hx : x with
  | mk XL XR =>
    simp
    simp [flatten_replicate_nil]

theorem Game.zero_mul (a : Game) : Game.mul zero a = zero := by
  apply wf_R.induction a
  intro x IH
  rw [zero]
  unfold mul
  match hx : x with
  | mk XL XR =>
    simp
    rfl

-------------------------------------------
--------------- a*b = b*a -----------------
-------------------------------------------
theorem mem_flatten_iff {α : Type} {x : α} {xss : List (List α)} :
    x ∈ flatten xss ↔ ∃ xs ∈ xss, x ∈ xs := by
  induction xss with
  | nil => simp [flatten]
  | cons h t ih => simp [flatten, List.mem_append, ih]


theorem mul_term_comm_aux (x y xl yl : Game)
  (IH_xyl : (x.mul yl).eq (yl.mul x))
  (IH_xly : (xl.mul y).eq (y.mul xl))
  (IH_xlyl : (xl.mul yl).eq (yl.mul xl)) :
  (((xl.mul y).add (x.mul yl)).add (xl.mul yl).neg).eq
  (((yl.mul x).add (y.mul xl)).add (yl.mul xl).neg) := by
  apply Game.add_equal
  constructor
  · have h : ((xl.mul y).add (x.mul yl)).eq ((x.mul yl).add (xl.mul y)) := by
      exact Game.add_comm
    refine Game.eq_trans  ⟨h, ?_⟩
    apply Game.add_equal
    constructor
    · exact IH_xyl
    · exact IH_xly
  · apply (Game.neg_congr).mp
    apply Game.eq_refl
    exact IH_xlyl


lemma Game.bigame_mul_comm (x : BiGame) : ((x.a).mul x.b).eq ((x.b).mul x.a) := by
  apply wf_B.induction x
  intro x IH
  match ha : x.a, hb : x.b with
  | mk AL AR, mk BL BR =>
    apply Game.eq_of_equiv_options
    -- ==========================================================
    -- CASE 1: Left Options Forward (x * y).left ⊆ (y * x).left
    -- ==========================================================
    {
      intro g hg
      dsimp only [Game.left] at hg
      rw [Game.mul, ← ha, ← hb] at hg; dsimp only [Game.left] at hg
      rw [List.mem_append] at hg
      rcases hg with hg_left | hg_right
      -- Subcase 1A: g from AL * BL
      {
        rw [mem_flatten_iff] at hg_left; rcases hg_left with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨la, h_la, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨lb, h_lb, rfl⟩
        exists ((lb.val.mul x.a).add (x.b.mul la.val)).add (lb.val.mul la.val).neg
        have h_a : la.val ∈ x.a.left := by rw [ha]; simp [Game.left]; exact la.property
        have h_b : lb.val ∈ x.b.left := by rw [hb]; simp [Game.left]; exact lb.property
        constructor
        · -- Show witness exists in (y * x).left
          rw [Game.mul, ha, hb]; dsimp only [Game.left]
          rw [List.mem_append]; apply Or.inl
          rw [mem_flatten_iff]
          exists (List.map (fun (la' : {x // x ∈ AL}) =>
             ((lb.val.mul x.a).add (x.b.mul la'.val)).add (lb.val.mul la'.val).neg) AL.attach)
          constructor
          · rw [ha, hb]
            apply List.mem_map_of_mem; exact h_lb
          · rw [ha, hb]
            apply List.mem_map_of_mem; exact h_la
        · dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.a, b := lb}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_left h_b)
            exact IH_call
          · have IH_call := IH {a := la, b := x.b}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_left h_a)
            exact IH_call
          · have IH_call := IH {a := la, b := lb}
            dsimp [B] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_left h_a) (birthday_lt_left h_b))
            exact IH_call
      }

      -- Subcase 1B: g from XR * YR
      {
        rw [mem_flatten_iff] at hg_right; rcases hg_right with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨ra, h_ra, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨rb, h_rb, rfl⟩
        -- Witness: The corresponding term in (y * x).left (YR * XR)
        exists ((rb.val.mul x.a).add (x.b.mul ra.val)).add (rb.val.mul ra.val).neg
        have h_a : ra.val ∈ x.a.right := by rw [ha]; simp [Game.right]; exact ra.property
        have h_b : rb.val ∈ x.b.right := by rw [hb]; simp [Game.right]; exact rb.property
        constructor
        · -- Show witness exists in (y * x).left (second part)
          rw [Game.mul, hb, ha]; dsimp only [Game.left]
          rw [List.mem_append]; apply Or.inr
          rw [mem_flatten_iff]
          exists (List.map (fun (ra' : {x // x ∈ AR}) =>
             ((rb.val.mul x.a).add (x.b.mul ra'.val)).add (rb.val.mul ra'.val).neg) AR.attach)
          constructor
          · rw [ha, hb]
            apply List.mem_map_of_mem
            exact h_rb
          · rw [ha, hb]
            apply List.mem_map_of_mem; exact h_ra
        · dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.a, b := rb}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_right h_b)
            exact IH_call
          · have IH_call := IH {a := ra, b := x.b}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_right h_a)
            exact IH_call
          · have IH_call := IH {a := ra, b := rb}
            dsimp [B] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_right h_a) (birthday_lt_right h_b))
            exact IH_call
      }
    }
   -- ==========================================================
    -- CASE 2: Left Options Backward (y * x).left ⊆ (x * y).left
    -- ==========================================================
    {
      intro g hg
      dsimp only [Game.left] at hg
      rw [Game.mul, ← ha, ← hb] at hg; dsimp only [Game.left] at hg
      rw [List.mem_append] at hg
      rcases hg with hg_left | hg_right
      -- Subcase 2A: g from YL * XL (matches Part 1 of Target)
      {
        rw [mem_flatten_iff] at hg_left; rcases hg_left with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨lb, h_lb, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨la, h_la, rfl⟩
        exists ((la.val.mul x.b).add (x.a.mul lb.val)).add (la.val.mul lb.val).neg
        have h_a : la.val ∈ x.a.left := by rw [ha]; simp [Game.left]; exact la.property
        have h_b : lb.val ∈ x.b.left := by rw [hb]; simp [Game.left]; exact lb.property
        constructor
        · rw [Game.mul, ha, hb]; dsimp only [Game.left]
          rw [List.mem_append]; apply Or.inl
          rw [mem_flatten_iff]
          exists (List.map (fun (lb' : {x // x ∈ BL}) =>
             ((la.val.mul x.b).add (x.a.mul lb'.val)).add (la.val.mul lb'.val).neg) BL.attach)
          constructor
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_la
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_lb
        · apply Game.eq_refl
          dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.a, b := lb}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_left h_b)
            exact IH_call
          · have IH_call := IH {a := la, b := x.b}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_left h_a)
            exact IH_call
          · have IH_call := IH {a := la, b := lb}
            dsimp [B] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_left h_a) (birthday_lt_left h_b))
            exact IH_call
      }
      {
        rw [mem_flatten_iff] at hg_right; rcases hg_right with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨rb, h_rb, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨ra, h_ra, rfl⟩
        have h_a : ra.val ∈ x.a.right := by rw [ha]; simp [Game.right]; exact ra.property
        have h_b : rb.val ∈ x.b.right := by rw [hb]; simp [Game.right]; exact rb.property
        exists ((ra.val.mul x.b).add (x.a.mul rb.val)).add (ra.val.mul rb.val).neg
        constructor
        · rw [Game.mul, ha, hb]; dsimp only [Game.left]
          rw [List.mem_append]; apply Or.inr
          rw [mem_flatten_iff]
          exists (List.map (fun (rb' : {x // x ∈ BR}) =>
             ((ra.val.mul x.b).add (x.a.mul rb'.val)).add (ra.val.mul rb'.val).neg) BR.attach)
          constructor
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_ra
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_rb
        · apply Game.eq_refl
          dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.a, b := rb}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_right h_b)
            exact IH_call
          · have IH_call := IH {a := ra, b := x.b}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_right h_a)
            exact IH_call
          · have IH_call := IH {a := ra, b := rb}
            dsimp [B] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_right h_a) (birthday_lt_right h_b))
            exact IH_call
      }
    }

    -- ==========================================================
    -- CASE 3: Right Options Forward (x * y).right ⊆ (y * x).right
    -- ==========================================================
    {
      intro g hg
      dsimp only [Game.right] at hg
      rw [Game.mul, ← ha, ← hb] at hg; dsimp only [Game.right] at hg
      rw [List.mem_append] at hg
      rcases hg with hg_left | hg_right
      -- Subcase 3A: g comes from (XL × YR)
      {
        rw [mem_flatten_iff] at hg_left; rcases hg_left with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨la, h_la, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨rb, h_rb, rfl⟩
        have h_a : la.val ∈ x.a.left := by rw [ha]; simp [Game.left]; exact la.property
        have h_b : rb.val ∈ x.b.right := by rw [hb]; simp [Game.right]; exact rb.property
        exists ((rb.val.mul x.a).add (x.b.mul la.val)).add (rb.val.mul la.val).neg
        constructor
        · rw [Game.mul, ha, hb]; dsimp only [Game.right]
          rw [List.mem_append]; apply Or.inr
          rw [mem_flatten_iff]
          exists (List.map (fun (la' : {x // x ∈ AL}) =>
             ((rb.val.mul x.a).add (x.b.mul la'.val)).add (rb.val.mul la'.val).neg) AL.attach)
          constructor
          · rw [ha, hb]
            apply List.mem_map_of_mem
            exact h_rb
          · rw [ha, hb]
            apply List.mem_map_of_mem
            exact h_la
        · dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.a, b := rb}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_right h_b)
            exact IH_call
          · have IH_call := IH {a := la, b := x.b}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_left h_a)
            exact IH_call
          · have IH_call := IH {a := la, b := rb}
            dsimp [B] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_left h_a) (birthday_lt_right h_b))
            exact IH_call
      }

      -- Subcase 3B: g comes from (XR × YL)
      {
        rw [mem_flatten_iff] at hg_right; rcases hg_right with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨ra, h_ra, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨lb, h_lb, rfl⟩
        have h_a : ra.val ∈ x.a.right := by rw [ha]; simp [Game.right]; exact ra.property
        have h_b : lb.val ∈ x.b.left := by rw [hb]; simp [Game.left]; exact lb.property
        exists ((lb.val.mul x.a).add (x.b.mul ra.val)).add (lb.val.mul ra.val).neg
        constructor
        · rw [Game.mul, ha, hb]; dsimp only [Game.right]
          rw [List.mem_append]; apply Or.inl
          rw [mem_flatten_iff]
          exists (List.map (fun (ra' : {x // x ∈ AR}) =>
             ((lb.val.mul x.a).add (x.b.mul ra'.val)).add (lb.val.mul ra'.val).neg) AR.attach)
          constructor
          · rw [ha, hb]
            apply List.mem_map_of_mem; exact h_lb
          · rw [ha, hb]
            apply List.mem_map_of_mem; exact h_ra
        · dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.a, b := lb}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_left h_b)
            exact IH_call
          · have IH_call := IH {a := ra, b := x.b}
            dsimp [B] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_right h_a)
            exact IH_call
          · have IH_call := IH {a := ra, b := lb}
            dsimp [B] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_right h_a) (birthday_lt_left h_b))
            exact IH_call
      }
    }
    -- ==========================================================
    -- CASE 4: Right Options Backward (y * x).right ⊆ (x * y).right
    -- ==========================================================
    {
      intro g hg
      dsimp only [Game.right] at hg
      rw [Game.mul, ← ha, ← hb] at hg; dsimp only [Game.right] at hg
      rw [List.mem_append] at hg
      rcases hg with hg_left | hg_right

      -- Subcase 4A: g from (YL * XR) -> Matches Part 2 of Target (XR * YL)
      {
        rw [mem_flatten_iff] at hg_left; rcases hg_left with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨lb, h_lb, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨ra, h_ra, rfl⟩
        have h_a : ra.val ∈ x.a.right := by rw [ha]; simp [Game.right]; exact ra.property
        have h_b : lb.val ∈ x.b.left := by rw [hb]; simp [Game.left]; exact lb.property
        exists ((ra.val.mul x.b).add (x.a.mul lb.val)).add (ra.val.mul lb.val).neg
        constructor
        · rw [Game.mul, ha, hb]; dsimp only [Game.right]
          rw [List.mem_append]; apply Or.inr
          rw [mem_flatten_iff]
          exists (List.map (fun (lb' : {x // x ∈ BL}) =>
             ((ra.val.mul x.b).add (x.a.mul lb'.val)).add (ra.val.mul lb'.val).neg) BL.attach)
          constructor
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_ra
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_lb
        · dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.b, b := ra}
            dsimp [B] at IH_call
            rw [Nat.add_comm x.a.birthday x.b.birthday] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_right h_a)
            exact IH_call
          · have IH_call := IH {a := lb, b := x.a}
            dsimp [B] at IH_call
            rw [Nat.add_comm x.a.birthday x.b.birthday] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_left h_b)
            exact IH_call
          · have IH_call := IH {a := lb, b := ra}
            dsimp [B] at IH_call
            rw [Nat.add_comm x.a.birthday x.b.birthday] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_left h_b) (birthday_lt_right h_a))
            exact IH_call
      }
      -- Subcase 4B: g from (YR * XL) -> Matches Part 1 of Target (XL * YR)
      {
        rw [mem_flatten_iff] at hg_right; rcases hg_right with ⟨inner, h_out, g_in⟩
        rw [List.mem_map] at h_out; rcases h_out with ⟨rb, h_rb, rfl⟩
        rw [List.mem_map] at g_in; rcases g_in with ⟨la, h_la, rfl⟩
        have h_a : la.val ∈ x.a.left := by rw [ha]; simp [Game.left]; exact la.property
        have h_b : rb.val ∈ x.b.right := by rw [hb]; simp [Game.right]; exact rb.property
        exists ((la.val.mul x.b).add (x.a.mul rb.val)).add (la.val.mul rb.val).neg
        constructor
        · rw [Game.mul, ha, hb]; dsimp only [Game.right]
          rw [List.mem_append]; apply Or.inl
          rw [mem_flatten_iff]
          exists (List.map (fun (rb' : {x // x ∈ BR}) =>
             ((la.val.mul x.b).add (x.a.mul rb'.val)).add (la.val.mul rb'.val).neg) BR.attach)
          constructor
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_la
          · rw [ha, hb]; apply List.mem_map_of_mem; exact h_rb
        · dsimp
          apply mul_term_comm_aux
          · have IH_call := IH {a := x.b, b := la}
            dsimp [B] at IH_call
            rw [Nat.add_comm x.a.birthday x.b.birthday] at IH_call
            rw [add_lt_add_iff_left] at IH_call
            specialize IH_call (birthday_lt_left h_a)
            exact IH_call
          · have IH_call := IH {a := rb, b := x.a}
            dsimp [B] at IH_call
            rw [Nat.add_comm x.a.birthday x.b.birthday] at IH_call
            rw [add_lt_add_iff_right] at IH_call
            specialize IH_call (birthday_lt_right h_b)
            exact IH_call
          · have IH_call := IH {a := rb, b := la}
            dsimp [B] at IH_call
            rw [Nat.add_comm x.a.birthday x.b.birthday] at IH_call
            specialize IH_call (add_lt_add (birthday_lt_right h_b) (birthday_lt_left h_a))
            exact IH_call
      }
    }


theorem Game.mul_comm {a b : Game} : (a.mul b).eq (b.mul a) := by
  let bi : BiGame := {a := a, b := b}
  apply Game.bigame_mul_comm bi

-------------------------------------------
------ (a = c and b = d) → a*b = c*d ------
-------------------------------------------
theorem Game.mul_equal {a b c d : Game} :
(a.eq c) ∧ (b.eq d) → (a.mul b).eq (c.mul d) := by
  sorry


-------------------------------------------
----- a, b IsSurreal → a*b IsSurreal ------
-------------------------------------------
theorem Surreal.mul_isSurreal {a b : Surreal} : IsSurreal (Game.mul a.val b.val) := by
  sorry


def Surreal.mul (a b : Surreal) :
  Surreal := ⟨(a.val).mul b.val, Surreal.mul_isSurreal⟩

-------------------------------------------
--------------- a*1 = 1 -------------------
-------------------------------------------

theorem Game.neg_zero : zero.neg = zero := by
  rw [Game.neg]
  simp [zero]
  unfold Game.right Game.left
  simp

-- Related lemma for mul_one
lemma flatten_map_singleton {α β} (l : List α) (f : α → β) :
  flatten (l.map (fun x => [f x])) = l.map f := by
  induction l with
  | nil => simp [flatten]
  | cons h t ih => simp [flatten, ih]

theorem Game.mul_one_eq {a : Game} : Game.mul a one = a := by
  apply wf_R.induction a
  intro x IH
  unfold R at IH
  rw [one]
  unfold mul
  match hx : x with
  | mk XL XR =>
    simp [flatten_replicate_nil]
    simp [zero]
    rw [flatten_map_singleton]
    rw [flatten_map_singleton]
    constructor
    · rw [map_id_iff,← zero, ← one, ← hx]
      intro lx lx_
      simp [Game.mul_zero, Game.add_zero, Game.neg_zero]
      apply IH
      exact birthday_lt_left lx_

    · rw [map_id_iff,← zero, ← one, ← hx]
      intro rx rx_
      simp [Game.mul_zero, Game.add_zero, Game.neg_zero]
      apply IH
      exact birthday_lt_right rx_


theorem Game.mul_one {a : Game} : (Game.mul a one).eq a := by
    unfold eq
    rw [Game.mul_one_eq]
    exact ⟨Game.le_congr, Game.le_congr⟩

theorem Game.one_mul {a : Game} : (Game.mul one a).eq a := by
  exact Game.eq_trans ⟨Game.mul_comm, Game.mul_one⟩


-------------------------------------------
----------- (a*b)*c = a*(b*c) -------------
-------------------------------------------

-- The proof shall be quite involved. May need AI to help.
theorem Game.mul_assoc {a b c : Game} :
  (Game.mul (Game.mul a b) c).eq (Game.mul a (Game.mul b c)) := by
  sorry


-------------------------------------------
---------- a*(b+c) = a*b + a*c ------------
-------------------------------------------
theorem Game.mul_distrib {a b c : Game} :
    Game.mul a (Game.add b c) = Game.add (Game.mul a b) (Game.mul a c) := by
  sorry
