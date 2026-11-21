import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def canonicalGaussianTreeGaugeStatement : Prop :=
  ∀ (L : ℕ) [NeZero L] (a : ℝ), Odd L → 0 ≤ a → ∀ (s n : ℕ) [NeZero n], 2 ≤ n →
    ∃ μ : Measure (LevelChain L s n), IsCanonicalGaussian (levelEnergy a s n) μ ∧
      ∀ᵐ X ∂μ, IsTreeGauge s n X
end YangMills.Construction.MomentLaw
end
