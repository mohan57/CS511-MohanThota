  import Mathlib.Data.Real.Basic
  import Mathlib.Tactic.IntervalCases
  import Library.Theory.Comparison
  import Library.Theory.Parity
  import Library.Theory.Prime
  import Library.Tactic.ModCases
  import Library.Tactic.Extra
  import Library.Tactic.Numbers
  import Library.Tactic.Addarith
  import Library.Tactic.Cancel
  import Library.Tactic.Use

  -- 5a
example : ∃! z : ℚ, ∀ b, b ≥ 1 → b ≤ 3 → (b - z) ^ 2 ≤ 1 := by
  use 2
  constructor
  intro b hb1 hb2
  have hb1 : -1 ≤ b - 2 := by 
    calc 
      -1 = 1 - 2 := by ring
      _ ≤ b - 2 := by addarith[hb1]
  have hb2 : b - 2 ≤ 1 := by 
    calc 
      b - 2 ≤ 3 - 2 := by addarith[hb2]
      _ = 1:= by ring
  calc 
      (b - 2) ^ 2 ≤ 1 ^ 2 := by apply sq_le_sq' hb1 hb2
        _  = 1 := by ring
  intro z hyz
  have h1 : (1 - z) ^ 2 ≤ 1 := hyz 1 (by simp) (by simp)
  have h3 : (3 - z) ^ 2 ≤ 1 := hyz 3 (by simp) (by simp)
  have h12 : (z - 2) ^ 2 ≤ 0 ^ 2 := by
    calc
        (z - 2) ^ 2 = ((1 - z) ^ 2 + (3 - z) ^ 2 - 2) / 2 := by ring
        _ ≤ (1 + (3 - z) ^ 2 - 2) / 2                    := by rel[h1]
        _ ≤ (1 + 1 - 2) / 2                              := by rel[h3]
        _ = 0 ^ 2                                       := by ring
  have h11 : 0 ≤ z - 2 ∧ z - 2 ≤ 0 := by apply abs_le_of_sq_le_sq' h12 (by addarith)
  exact le_antisymm (by addarith[h11.right]) (by addarith[h11.left])

--5b
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  constructor
  · numbers
  intro y hy
  have key : 4 * y = 12 := by
    calc 
      4 * y = 4 * y - 3 + 3 := by ring
          _ = 9 + 3 := by rw[hy]
          _ = 12 := by ring
  have y_eq_3 : y = 3 := by 
    calc 
      y = 4 * y / 4 := by ring
      _ = 12 / 4 := by rw [key] 
       _ = 3      := by numbers
  exact y_eq_3

--5c
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  constructor
  · intro a
    extra
  intro y hy
  have h0 : 0 ≤ y :=by extra
  have h1 : y ≤ 0 :=hy 0
  exact le_antisymm h1 h0