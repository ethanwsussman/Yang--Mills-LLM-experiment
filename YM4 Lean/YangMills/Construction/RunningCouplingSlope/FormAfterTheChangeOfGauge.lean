import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def FibreHessianAfterGaugeChange : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
      ∀ W : Tower.Edge L n k k → Matrices.ComplexMatrix2, RepresentsTorusField W V →
      ∀ X : ChainPoint L n k, IsMinimizerOver a W X →
        ∀ (J : LevelForms L n k) (μ : Tower.edgeFormSpace L n k k),
          IsLevelGradient (chainAction a) X J → IsTopMultiplier X J μ →
          ∀ ξ ∈ LinearMap.ker (shiftedGaugeMap X),
            ∃ η : LinearMap.ker (topDeriv X), (η : LevelForms L n k) = gaugeTransform X ξ ∧
              fibreHessian a X η = gaugedFormValue a X J μ ξ
end YangMills.Construction.RunningCouplingSlope
end
