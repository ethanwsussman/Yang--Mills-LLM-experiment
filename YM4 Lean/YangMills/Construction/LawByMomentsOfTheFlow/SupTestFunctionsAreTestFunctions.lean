import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
def supTestFamilyIsTestFamilyStatement : Prop :=
  ∀ (k : ℕ) (R d : ℝ) (φ : Fin k → TestFunctions.EuclideanFourSpace → ℝ),
    IsSupTestFamily R d φ → TestFunctions.IsSeparatedLipschitzFamily (2 * R) d φ
end YangMills.Construction.MomentLaw
end
