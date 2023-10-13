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

--Problem 4--
  --3.1.4
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc 
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw[hk] 
    _ = 2*(7*k + 1) + 1 := by ring 

--3.1.6
  example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    use 2 *a * b + 3* b + a + 1
    calc 
      x*y +2*y = (2*a+1) * (2*b+1) + 2 * (2*b+1) := by rw[ha,hb]
      _ = 2 * (2 *a * b + 3* b + a + 1)  + 1 := by ring
  
--3.1.7
example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  dsimp[Even] at *
  obtain ⟨t, ht⟩ := hm
  use 3 * t - 1
  calc 
    3 * m - 5 = 3 * (2*t +1) -5 := by rw[ht]
    _ = 3 *t - 1 + (3 *t -1) :=by ring


-- 3.1.8
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp[Even] at *
  obtain ⟨t, ht⟩ := hn
  use 2 * (t ^ 2 + 1*t) -3
  calc 
    n ^ 2 + 2 * n - 5 = (t +t)^2 + 2 * (t +t) - 5 := by rw[ht] 
    _ = 2 * (2 * (t ^ 2 + 1*t) - 3) + 1 := by ring 

--3.1.10

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha | ha := Int.even_or_odd a
  obtain hb | hb := Int.even_or_odd b
  left 
  obtain ⟨x, hx⟩ := ha 
  obtain ⟨y, hy⟩ := hb
  use x - y
  calc 
    a - b = 2 * x - 2 * y := by rw [hx, hy]
    _ = 2 * (x - y) := by ring
  right
  left
  obtain ⟨x, hx⟩ := ha 
  obtain ⟨y, hy⟩ := hb
  use x + (2*y + 1)
  calc
    a + c = 2 * x + (2*y + 1) := by rw [hx, hy]
    _ = 2 * (x + y + 1) := by ring
  obtain hc | hc := Int.even_or_odd c
  right 
  left
  obtain ⟨x, hx⟩ := ha 
  obtain ⟨z, hz⟩ := hc
  use (2*x + 1) + z
  calc
    a + c = (2*x + 1) + 2*z := by rw [hx, hz]
    _ = 2 * (x + z + 1) := by ring
  right 
  right 
  obtain ⟨y, hy⟩ := Int.even_or_odd b 
  obtain ⟨z, hz⟩ := hc
  use (2*y + 1) - (2*z + 1)
  calc
    b - c = (2*y + 1) - (2*z + 1) := by rw [hy, hz]
    _ = 2 * (y - z) := by ring





--Problem 5--
-- 4.1.4
example {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) :
    a = b := by
  apply le_antisymm
  · apply hb2
    apply ha1
  · apply ha2
    apply hb1

--4.1.3
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  obtain h1 | h2 := h (a + b / 2)
  · apply le_of_not_gt 
    simp 
    exact

-- 4.1.6
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y
  intro h1
  · apply abs_le_of_sq_le_sq'
    calc
      (x + y) ^ 2 ≤ (x +y)^2 + (x-y)^2 := by addarith [h1]
      _ = 2 (x^2 + y^2 ):= by ring
      _ ≤ 2 * 4 := by rw [h1]
      _ ≤ 3 ^ 2  := by extra

  
--4.1.10 (2)

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n :=
  have h1 : 1 ≤ 5 := by numbers
  have h2 : 1 ≤ 15 := by numbers
  have h3 : 5 ≤ 15 := by numbers
  apply hn 15 h2 h3