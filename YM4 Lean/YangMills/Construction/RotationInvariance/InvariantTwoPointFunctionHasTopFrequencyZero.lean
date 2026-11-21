import YangMills.Construction.EuclideanFunctionals.InvarianceOfTheMomentsAndReductionToTheTimePlane
import YangMills.Construction.RotationInvariance.ComplexTuplesAndPlaneData
import YangMills.Construction.RotationInvariance.TopFrequencyOfTheHarmonics
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency
open MomentSymmetry
def InvariantNearZero (S : ConnFamily) : Prop :=
  ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, |t| < t₀ → TwoPointInvariant S (rotateMotion t)
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (_data : ProductPlaneData m S)
    (φ₀ : YangMills.Construction.RealPlane.openingAngles),
    InvariantNearZero S → maxFrequency S φ₀ 2 = 0
end YangMills.Construction.EuclideanFunctionals.TwoPointTopFrequency
end
