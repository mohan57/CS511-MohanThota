import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

--2.5.2

example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' : 0 < -(x * t):= by addarith [hxt] 
    have  hxt'' : -(x * t) = x * (-t) := by ring
    have hx' : 0 < x := by addarith[hx]
    rw [hxt''] at hxt'
    cancel x at hxt'
    have : t < 0 := by simpa using hxt'
    exact ne_of_lt this


-- 2.5.6
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
 use a+1,a
 calc 
  (a + 1) ^ 2 - a ^ 2 = (a^2 + 2*a + 1) - a^2 :=by ring
  _= 2 * a + 1 :=by ring

-- 2.5.7 used linarith to try out its functionality for just this problem.
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  have hpq : p < (p + q) / 2 := by linarith
  have hpq' : (p + q) / 2 < q := by linarith
  use  (p+q)/2
  constructor
  · exact hpq
  · exact hpq'