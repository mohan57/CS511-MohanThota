import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use


--5.3.6.9
example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  intro hp
  have h1 : k ∣ p := hk
  have h2 : k ≠ 1 := hk1
  have h3 : k ≠ p := hkp
  use k
  exact ⟨h1, ⟨h2, h3⟩⟩

--5.3.6.10
example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H'
    apply hp
    apply prime_test hp2
    exact H'

  push_neg at H
  obtain ⟨m, h2, h3, h4⟩ := H
  use m
  exact ⟨h2, h3, h4⟩
