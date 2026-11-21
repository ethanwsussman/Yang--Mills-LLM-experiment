import YangMills.Construction.RotationInvariance.ComplexTuplesAndPlaneData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.PlaneDataAsStandingData
variable {M : SharpScale} {S : ConnFamily}
def Matches (d : ProductPlaneData M S) (s : PlaneStandingData M S) : Prop :=
  s.frac = d.fraction ∧ s.sigma = d.fnl ∧ s.expo = d.exponent ∧
    s.labelConst = d.labelBound
def ExistsStandingAndApertureData : Prop :=
  ∀ (M : SharpScale) (S : ConnFamily) (d : ProductPlaneData M S),
    (∃ s : PlaneStandingData M S, Matches d s) ∧
    ∀ α : RealPlane.openingAngles, ∃ e : PlaneDataWithAperture M S,
      Matches d e.base ∧ e.angle = α
end YangMills.Construction.EuclideanFunctionals.PlaneDataAsStandingData
end
