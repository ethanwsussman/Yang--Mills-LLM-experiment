import YangMills.Construction.RotationInvariance.TopFrequencyOfTheHarmonics
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals.MaxFrequencyLaw
def Holds : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S),
    (∀ k : ℕ, maxFrequency S d.angle (2 * k) = k * maxFrequency S d.angle 2) ∧
    (∀ n : ℕ, (maxFrequency S d.angle n : ℝ) ≤ (n : ℝ) / 2 * (maxFrequency S d.angle 2 : ℝ))
end EuclideanFunctionals.MaxFrequencyLaw
end YangMills.Construction
end
