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


--4.a
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  intro h
  constructor
  obtain ⟨ k, hk⟩ := h
  use 9 * k
  calc
    n = 63 * k := by rw [hk]
    _ = 7 * (9 * k) := by ring
  obtain ⟨ k,hk ⟩ := h
  use 7 * k
  calc
    n = 63 * k := by rw[hk]
    _ = 9 * (7 * k) := by ring
  intro h1
  obtain⟨ ha ,hb ⟩ := h1
  obtain⟨a, ha_eq⟩ := ha
  obtain⟨b, hb_eq⟩ := hb
  use 4 * b - 3 * a
  calc
      n = 4 * 7 * n - 3 * 9 * n := by ring
      _ = 4 * 7 * n - 3 * 9 * (7 * a) := by rw[ha_eq]
      _ = 4 * 7 * (9 * b) - 3 * 9 * (7 * a) := by rw[hb_eq]
      _ = 252 * b - 189 * a := by ring
      _ = 63 * (4 * b - 3 * a) := by ring

-- 4.b
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  intro h
  have bound : k ^ 2 < 3 ^ 2 := by
    calc
      k ^ 2 ≤ 6      := by rel[h]
      _ < 6 + 3  := by extra
      _ = 9      := by numbers
  have k_lt_3 : k < 3 := by
    cancel 2 at bound
  interval_cases k
  left 
  numbers
  right; left; numbers
  right; right; numbers
  intro h_cases
  obtain hk0 | hk_other := h_cases
  rw[hk0]
  numbers
  obtain hk1 | hk2 := hk_other
  rw[hk1] 
  numbers
  rw[hk2]
  numbers