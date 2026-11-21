import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsOfSeparatedFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace SeparatedMoments
open ChessboardTori
def CoarseCaseMomentBound : Prop :=
  ∀ (D : ChessboardSetup) (M R d l : ℝ) (n : ℕ), 1 ≤ M → 0 < R → 0 < d → d ≤ 1 → 2 ≤ n →
    IsMaximalScalePower D.L d l → l / D.mesh < max (2 ^ 6 * (n : ℝ)) ((D.L : ℝ) ^ 2) →
      CentredMomentBound D M R d (coarseConstant D.L R n d) n
end SeparatedMoments
end YangMills.Construction
end
