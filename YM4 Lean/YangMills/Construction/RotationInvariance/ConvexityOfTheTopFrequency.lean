import YangMills.Construction.RotationInvariance.TopFrequencyOfTheHarmonics
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals.MaxFrequencyConvex
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S) (k l : ℕ),
    2 * maxFrequency S d.angle (k + l) ≤
      maxFrequency S d.angle (2 * k) + maxFrequency S d.angle (2 * l)
end EuclideanFunctionals.MaxFrequencyConvex
end YangMills.Construction
end
