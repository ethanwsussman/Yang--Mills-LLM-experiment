import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower
def MinimizerGaugeEquivalentToSmallMove : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ (N : ℕ) (e : (Fin N → ℝ) ≃ₗ[ℝ] LevelForms L n k) (O : Set (Fin N → ℝ)), O ∈ 𝓝 0 →
      ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)), ∀ W : Edge L n k k → Matrices.ComplexMatrix2,
        RepresentsTorusField W V →
        ∀ X : ChainPoint L n k, IsMinimizerOver a W X →
          ∃ (v : Vertex L n k 0 → Matrices.ComplexMatrix2) (w : Fin N → ℝ),
            (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) ∧
            (∀ y : Vertex L n k k, restrictVertexFunction k v y = 1) ∧ w ∈ O ∧
            gaugeTransformPoint v X = expMove (e w) (unitPoint L n k)
end RunningCouplingSlope
end YangMills.Construction
end
