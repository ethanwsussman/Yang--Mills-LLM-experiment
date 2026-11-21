import YangMills.Construction.LawByMomentsOfTheFlow.MomentsOfTheCurvatureInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ContourMeans
theorem blockCentreSite_add {n L : ℕ} [NeZero n] [NeZero L] (Y : TorusFields.TorusSite n) (v : Fin 4 → ℤ) :
    TorusBlocks.blockCentreSite L (Y + TorusFields.siteOfInt v) =
      TorusBlocks.blockCentreSite L Y + TorusFields.siteOfInt fun i => (L : ℤ) * v i := by apply _root_.YangMills.SharedProofs.p20130 <;> assumption
end YangMills.Construction.ContourMeans
end
