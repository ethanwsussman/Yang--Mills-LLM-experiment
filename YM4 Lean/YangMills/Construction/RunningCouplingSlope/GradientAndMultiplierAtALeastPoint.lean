import YangMills.Construction.RunningCouplingSlope.TangentOfTheLastNoise
import YangMills.Construction.RunningCouplingSlope.TorusViewedOnATower
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def GradientAndMultiplierAtMinimizer : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m n : ℕ, 0 < n →
    ∀ᶠ V in 𝓝 (TorusFields.trivialField (2 * L ^ n)),
      ∀ W : Edge L n (m + 1) (m + 1) → Matrices.ComplexMatrix2, RepresentsTorusField W V →
      ∀ X : ChainPoint L n (m + 1), IsMinimizerOver a W X →
        ∃ (J : LevelForms L n (m + 1)) (μ : edgeFormSpace L n (m + 1) (m + 1)),
          IsLevelGradient (chainAction a) X J ∧ IsTopMultiplier X J μ ∧
          ∀ B : edgeFormSpace L n (m + 1) (m + 1),
            (edgeFormPairing (μ : Edge L n (m + 1) (m + 1) → Matrices.ComplexMatrix2)
              (B : Edge L n (m + 1) (m + 1) → Matrices.ComplexMatrix2)).re =
                leftDeriv (chainAction a) X (lastNoiseTangent B)
end YangMills.Construction.RunningCouplingSlope
end
