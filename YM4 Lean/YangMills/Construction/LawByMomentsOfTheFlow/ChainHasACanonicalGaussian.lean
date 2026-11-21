import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def canonicalGaussianExistsStatement : Prop :=
  ∀ (L : ℕ) [NeZero L] (a : ℝ), 0 ≤ a → ∀ (s n : ℕ) [NeZero n],
    ∃ μ : Measure (LevelChain L s n), IsCanonicalGaussian (levelEnergy a s n) μ
end YangMills.Construction.MomentLaw
end
