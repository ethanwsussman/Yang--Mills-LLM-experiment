import YangMills.Construction.RunningCouplingSlope.ExcessOfAStepForm
import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower BlockAverages ColdStepAtMirrorFrames TorusFields Conventions Matrices
def FibreHessianEqSumExcessHessians : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ᶠ U in 𝓝 (trivialField (2 * L ^ n)), ∀ W : Edge L n (k + 1) (k + 1) → ComplexMatrix2, RepresentsTorusField W U →
        ∀ X : ChainPoint L n (k + 1), IsMinimizerOver a W X → RepresentsMinimizerChain a ρ U X →
          ∀ ξ : LinearMap.ker (RunningCouplingSlope.topDeriv X),
            fibreHessian a X ξ = ∑ i : Fin (k + 1),
              excessHessian a (stepMinimizer a ρ (topFieldAtStep a ρ L n (k + 1) i U))
                (topFieldAtStep a ρ L n (k + 1) i U)
                (frameVelocityOfForm i (tangentTransport X (ξ : LevelForms L n (k + 1)) i))
                (frameVelocityOfForm (i + 1) (tangentTransport X (ξ : LevelForms L n (k + 1)) (i + 1)))
end RunningCouplingSlope
end YangMills.Construction
end
