import YangMills.Construction.Continuum.KernelsOfTheParametrix
import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.Parametrix
open EuclideanFunctionals MeasureTheory
def OriginIdentity : Prop :=
  ∀ φ : R4 → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∫ x, (innerKernelUnit x : ℂ) * TestFunctions.laplacianR4^[3] φ x =
      φ 0 - ∫ x, (outerKernelUnit x : ℂ) * φ x
end YangMills.Construction.Parametrix
