import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def FibreHessianAtMinimizer : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
      ∀ W : Tower.Edge L n k k → Matrices.ComplexMatrix2, RepresentsTorusField W V →
      ∀ X : ChainPoint L n k, IsMinimizerOver a W X →
        (∀ ξ, 0 ≤ fibreHessian a X ξ) ∧
        ∀ ξ : LinearMap.ker (topDeriv X), fibreHessian a X ξ = 0 ↔
          (ξ : LevelForms L n k) ∈ (topVanishingGauges L n k).map (gaugeOrbitMap X)
end YangMills.Construction.RunningCouplingSlope
end
