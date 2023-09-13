-- Live WebAssembly version of Lean
import data.real.basic

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
begin
  calc
    a = a - 5 * b : by refl
  ... = 4 + 5 * b : by rw h1
  ... = 4 + 5 * (3 - 2) : by rw h2
  ... = 9 : by refl
end

