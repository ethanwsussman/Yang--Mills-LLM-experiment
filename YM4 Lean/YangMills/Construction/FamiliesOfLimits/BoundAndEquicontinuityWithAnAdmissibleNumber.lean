import YangMills.Construction.FamiliesOfLimits.FamiliesOfLimitsDefs
import YangMills.Construction.TorusOrFourSpace.SpaceQuotientMapAndDistance
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FamiliesOfLimits.LimitSetup
variable (D : LimitSetup)
def sharpNormTorus {ℓ : ℝ} (f : TorusMetric.Torus4 ℓ → ℝ) : ℝ :=
  TestFunctions.sharpNormTorus (D.choice.M : ℝ) f
def spaceParams (m : ℕ+) : PeriodicSpace.Params where
  L := D.L
  isAdmissible := D.standingConstraints.factor_admissible
  m := m
  M := (D.choice.M : ℝ)
  one_le_M := by exact_mod_cast D.toGrowth.one_le_M
end YangMills.Construction.FamiliesOfLimits.LimitSetup
end
