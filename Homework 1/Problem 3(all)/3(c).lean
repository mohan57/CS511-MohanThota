-- Live WebAssembly version of Lean

theorem example_proof (P Q R : Prop) (h1 : P ∧ ¬Q → R) (h2 : ¬R) (h3 : P) (h4 : ¬Q) : Q :=
begin
  have h5 : P ∧ ¬Q := ⟨h3, h4⟩,
  have h6 : R := h1 h5,
  contradiction,
end
