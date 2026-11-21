import YangMills.Construction.EuclideanFunctionals.JointSpectralMeasureOfAReconstructionAndTheConeCondition
import YangMills.Construction.EuclideanFunctionals.PlateBoundOfAFunctionalWithReconstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
open RealPlane
structure PlaneStandingData (m : SharpScale) (S : ConnFamily) where
  frac : ℝ
  frac_mem : frac ∈ productBoundFractions
  sigma : EuclidFunctionalWithRecon m S
  cone : sigma.ConeCondition
  expo : ℝ
  expo_pos : 0 < expo
  labelConst : realLabels → ℝ
  boundWith_labelConst : ∀ φ : realLabels,
    ProductBoundWith sigma expo_pos frac_mem φ.1 (labelConst φ)
theorem PlaneStandingData.productBoundWithExponent {m : SharpScale} {S : ConnFamily}
    (d : PlaneStandingData m S) :
    ProductBoundWithExponent d.sigma d.expo_pos d.frac_mem :=
  fun φ hφ => ⟨d.labelConst ⟨φ, hφ⟩, d.boundWith_labelConst ⟨φ, hφ⟩⟩
end YangMills.Construction.EuclideanFunctionals
