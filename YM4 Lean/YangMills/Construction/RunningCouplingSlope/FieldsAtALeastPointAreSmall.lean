import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower
def MinimizerFieldsNearOne : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)), ∀ W : Edge L n k k → Matrices.ComplexMatrix2,
        RepresentsTorusField W V →
        ∀ X : ChainPoint L n k, IsMinimizerOver a W X →
          (∀ j, j ≤ k → ∀ p : Face L n k j,
            Matrices.ComplexMatrix2.operatorNorm
              (PeriodicLattice.plaquetteHolonomy (levelField X j) p - 1) < ε) ∧
          (∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
            Matrices.ComplexMatrix2.operatorNorm (X.noise i c - 1) < ε) ∧
          ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
            ‖meanRadius (levelField X i) c.1 - 1‖ < ε
end RunningCouplingSlope
end YangMills.Construction
end
