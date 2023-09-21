-- Live WebAssembly version of Lean
import tactic.linarith
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
begin
  calc 
  x     = 2 - 4 : by linarith
    ... = -2    : by refl
end




