import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower
def MinimizersFormOneGaugeOrbit : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
      ∀ W : Edge L n k k → Matrices.ComplexMatrix2, RepresentsTorusField W V →
      ∀ X X' : ChainPoint L n k, IsMinimizerOver a W X → IsMinimizerOver a W X' →
        ∃ v : Vertex L n k 0 → Matrices.ComplexMatrix2,
          (∀ x, v x ∈ PeriodicLattice.compactGaugeGroup) ∧
          (∀ y : Vertex L n k k, restrictVertexFunction k v y = 1) ∧ X' = gaugeTransformPoint v X
end RunningCouplingSlope
end YangMills.Construction
end
