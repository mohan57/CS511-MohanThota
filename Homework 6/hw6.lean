  import Mathlib.Data.Real.Basic
  import Mathlib.Tactic.IntervalCases
  import Library.Theory.Comparison
  import Library.Theory.Parity
  import Library.Theory.Prime
  import Library.Tactic.ModCases
  import Library.Tactic.Extra
  import Library.Tactic.Numbers
  import Library.Tactic.Addarith
  import Library.Tactic.Cancel
  import Library.Tactic.Use
  
--5.1.7.11
  example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro h 
    obtain ⟨a, hP⟩ := h
    use a
    have hPQ : P a ↔ Q a := h a
    exact (hPQ.1 hP)
  · intro h
    obtain ⟨b, hQ⟩ := h
    use b
    have hQP : Q b ↔ P b := (h b).symm
    exact (hQP.1 hQ)

--5.1.7.12
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
constructor
· intro h
  obtain ⟨x1, y1, hP⟩ := h
  have xy : ∃ y x, P x y := ⟨y1, x1, hP⟩
  exact xy
· intro h
  obtain ⟨y2, x2, hP⟩ := h
  have yx : ∃ x y, P x y := ⟨x2, y2, hP⟩
  exact yx

--5.1.7.13
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro h 
    intro y1 x1
    exact h x1 y1
  · intro h
    intro x2 y2
    exact h y2 x2

--5.1.7.14
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro h
    have hP := h.left
    have hQ := h.right
    obtain ⟨x, hp⟩ := hP
    exact ⟨x, hp, hQ⟩
  · intro h
    obtain ⟨x, hP, hQ⟩ := h
    constructor
    · exact ⟨x, hP⟩
    · exact hQ





