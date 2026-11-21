import YangMills.Construction.GrowingTori.DataAndSequencesOfTheLimitsAlongGrowingTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
def LargeOddBlockingFactorsHaveLimitSetup : Prop :=
  ∃ bound : ℕ, ∀ L : ℕ, Odd L → bound ≤ L → ∃ D : ToriLimits.Setup, D.L = L
end YangMills.Construction.TotalDensitiesGiveASystem
end
