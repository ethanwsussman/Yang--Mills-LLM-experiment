import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
def levelEnergyCanonicalGaussianStatement : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∀ (L s n : ℕ) [NeZero L] [NeZero n],
    ∃ μ : Measure (LevelChain L s n), IsCanonicalGaussian (levelEnergy a s n) μ
end YangMills.Construction.MomentLaw
end
