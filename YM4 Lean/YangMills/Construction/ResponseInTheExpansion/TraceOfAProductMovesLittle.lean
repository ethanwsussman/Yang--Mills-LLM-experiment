import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MatrixTraces
def TraceProdLipschitz : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (q : ℕ) (M M' : Fin (q + 1) → Matrix Q Q ℝ) (a b : ℝ),
    0 ≤ a → 0 ≤ b → (∀ j x y, |M j x y| ≤ a) → (∀ j x y, |M' j x y| ≤ a) → (∀ j x y, |M j x y - M' j x y| ≤ b) →
    |Matrix.trace (List.ofFn M).prod - Matrix.trace (List.ofFn M').prod| ≤
      ((q : ℝ) + 1) * (Fintype.card Q : ℝ) ^ (q + 2) * a ^ q * b
end YangMills.Construction.MatrixTraces
end
