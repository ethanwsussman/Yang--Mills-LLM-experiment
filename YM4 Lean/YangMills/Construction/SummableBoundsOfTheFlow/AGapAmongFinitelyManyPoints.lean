import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.FiniteMetricGap
def ExistsGapAmongFinitePoints : Prop :=
  ∀ (n : ℕ) (X : Type) (dist : X → X → ℝ) (pt : Fin n → X) (a b : Fin n), 2 ≤ n →
    (∀ x, dist x x = 0) → (∀ x y, dist x y = dist y x) → (∀ x y z, dist x z ≤ dist x y + dist y z) →
    ∃ S : Finset (Fin n), S.Nonempty ∧ Sᶜ.Nonempty ∧
      ∀ i ∈ S, ∀ j ∉ S, dist (pt a) (pt b) / ((n : ℝ) - 1) ≤ dist (pt i) (pt j)
end YangMills.Construction.FiniteMetricGap
