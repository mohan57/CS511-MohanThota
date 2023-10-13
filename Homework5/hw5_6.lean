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


--a
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  apply hp 
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm1 | hm2 : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  left
  addarith [hm1]
  have h1 : m ≤ p := by apply Nat.le_of_dvd hp' hmp
  obtain h_left | h_right : m = p ∨ m < p := eq_or_lt_of_le h1
  right
  addarith [h_left]
  by_cases (m ∣ p)
  have h2 : ¬ m ∣ p := H m hm2 h_right
  contradiction
  contradiction

     

--c
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) : y ≤ x := by
  by_cases hxy : y ≤ x
  · exact hxy
  · push_neg at hxy
    have hy_pow : y ^ n > x ^ n := by rel[hxy]
    have hcontradiction : ¬(y ^ n > x ^ n) := not_lt_of_le h
    contradiction


--d
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain p_even | p_odd := Nat.even_or_odd p
  · obtain ⟨hmisc, hprime_dvd⟩ := h
    have h2_dvd_p : 2 ∣ p := p_even
    have h2_or := hprime_dvd 2 h2_dvd_p
    obtain h1_eq_2 | h2_eq_p := h2_or
    · contradiction
    · left
      rw[h2_eq_p]
  · right
    exact p_odd
