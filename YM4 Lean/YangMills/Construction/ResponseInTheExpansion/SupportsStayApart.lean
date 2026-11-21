import YangMills.Construction.ResponseInTheExpansion.CurvatureOnTheBareTorus
import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
def supportsSeparatedAtLowerLevels : Prop :=
  ∀ (L : ℕ) [NeZero L], Odd L → ∀ (K t n : ℕ) [NeZero n], t ≤ K → ∀ (d : ℝ) (h h' : PlaquetteWeight (fineSide L t n)),
    SupportsSeparated L K d h h' → ∀ Y ∈ thickening 2 (weightSupportSites L t n h),
      ∀ Y' ∈ thickening 2 (weightSupportSites L t n h'),
      d * (L : ℝ) ^ (K - t) - 5 ≤ supDist Y Y'
end YangMills.Construction.ResponseInTheExpansion
end
