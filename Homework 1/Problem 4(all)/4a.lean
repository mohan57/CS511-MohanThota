-- Live WebAssembly version of Lean

example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
begin
  calc 
  a     = 2 * b + 5 : h1
    ... = 2 * 3 + 5 : by rw h2
    ... = 6 + 5     : by refl
    ... = 11        : by refl
end

