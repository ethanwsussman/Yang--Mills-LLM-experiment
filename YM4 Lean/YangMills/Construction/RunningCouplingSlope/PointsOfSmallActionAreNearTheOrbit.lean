import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower
def SmallActionNearGaugeOrbit : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ChainPoint L n k, IsCompactValued X →
      (∀ b, Matrices.ComplexMatrix2.operatorNorm (levelField X k b - 1) < δ) → chainAction a X < δ →
      ∃ v : Vertex L n k 0 → Matrices.ComplexMatrix2, (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) ∧
        (∀ y : Vertex L n k k, restrictVertexFunction k v y = 1) ∧
        (∀ b, Matrices.ComplexMatrix2.operatorNorm ((gaugeTransformPoint v X).fine b - 1) < ε) ∧
        ∀ i c, Matrices.ComplexMatrix2.operatorNorm ((gaugeTransformPoint v X).noise i c - 1) < ε
end RunningCouplingSlope
end YangMills.Construction
end
