import YangMills.Construction.RotationInvariance.RadialBumpsAtALengthAndTheirFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
open scoped Pointwise
namespace EuclideanFunctionals.RadialMollifiers
def ExistAndConvergeC1 : Prop :=
  ∀ (m : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture m S) (η : ℝ),
    η ∈ Set.Ioc (0 : ℝ) 1 →
    (∃ δ : ℕ+ → RealPlane → ℝ, d.IsRadialMollifier η δ) ∧
    ∀ δ : ℕ+ → RealPlane → ℝ, d.IsRadialMollifier η δ →
      ∀ b ∈ complexProfiles, ∀ φ ∈ realLabels,
        (∀ j : ℕ+, convolve b (ofRealFun (δ j)) ∈ complexProfiles ∧
          tsupport (convolve b (ofRealFun (δ j))) ⊆
            tsupport b + closedDiscAt 0 (d.base.frac * η)) ∧
        TendstoC1
          (fun k : ℕ => RealPlane.productFunction (convolve b (ofRealFun (δ k.succPNat))) φ)
          (RealPlane.productFunction b φ)
end EuclideanFunctionals.RadialMollifiers
end YangMills.Construction
end
