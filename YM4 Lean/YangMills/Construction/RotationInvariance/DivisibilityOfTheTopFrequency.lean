import YangMills.Construction.RotationInvariance.TopFrequencyOfTheHarmonics
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals.MaxFrequencyDivisible
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S) (k : ℕ), 1 ≤ k →
    k ∣ 2 * maxFrequency S d.angle (2 * k)
end EuclideanFunctionals.MaxFrequencyDivisible
end YangMills.Construction
end
