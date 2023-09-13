-- Live WebAssembly version of Lean

theorem example_proof (P Q R : Prop) (h1 : P ∧ Q → R) (h2 : P) (h3 : Q) : P → (Q → R) :=
begin
  intros hp hq,
  have h_and : P ∧ Q := ⟨hp, hq⟩,
  exact h1 h_and,
end











