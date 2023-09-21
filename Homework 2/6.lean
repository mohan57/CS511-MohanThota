import Mathlib.Data.Real.Basic
import Library.Tactic.Addarith
import Library.Tactic.Numbers
import Library.Tactic.Extra

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x ≥ x * (x ^ 2 - 8 * x + 2) := by extra
    ≥ 3 := by rel[hx] 



