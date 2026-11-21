import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import YangMills.Construction.TestFunctions.LaplacianOfR4
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.Parametrix
open YangMills.Construction.EuclideanFunctionals
def LaplacianCubeSelfAdjoint : Prop :=
  ∀ (g : R4 → ℂ) (v : R4 → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g → ContDiff ℝ ∞ v →
    ∫ x, TestFunctions.laplacianR4^[3] g x * (v x : ℂ) =
      ∫ x, g x * Complex.ofReal (TestFunctions.laplacianR4^[3] v x)
end YangMills.Construction.Parametrix
