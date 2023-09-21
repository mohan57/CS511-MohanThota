import Mathlib.Data.Real.Basic
import Library.Tactic.Addarith
import Library.Tactic.Numbers
import Library.Tactic.Extra


--6 .a

example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc 
    x = x + 3 - 3 := by ring
    _ ≥ 2 * y - 3 := by rel [h1]
    _ ≥ 2 * 1 -3 := by rel [h2]
    _ ≥ -1 := by numbers


-- 6.b

example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc 
    a + b  = 2 * (a + b) / 2 := by ring  
    _ = (a + (a + 2 * b)) / 2 :=by ring
    _ ≥ ( a + 4)/2 := by rel[h2] 
    _ ≥ (3 + 4)/2 := by rel [h1]
    _ = 3.5 := by ring
    _ ≥ 3 := by numbers

-- 6. c

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x = x * x ^ 2 - 8 * x ^ 2 +2 * x := by ring
    _ ≥  9 *  x ^ 2 - 8 * x ^ 2 +2 * x := by rel[hx]
    _ = x * x + 2 * x := by ring
    _ ≥ 9 * x + 2 * x := by rel [hx]
    _ = 11 * x := by ring
    _ ≥ 11 * 9 := by rel[hx] 
    _ ≥ 3 := by numbers






  






