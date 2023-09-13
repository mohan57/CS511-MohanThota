-- Live WebAssembly version of Lean

theorem example_proof (P Q R : Prop) (h1 : P → (Q → R)) (h2 : P → Q) (h3 : P) : (P → Q) → (P → R) :=
begin
  intro h4, 
  intro h5, 
  have h6 : Q := h2 h5, 
  have h7 : R := h1 h5 h6, 
  exact h7, 
end
