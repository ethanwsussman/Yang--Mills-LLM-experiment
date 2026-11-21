import YangMills.Construction.RotationInvariance.PlaneDataAreDataOfTheTwoSettings
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.PlaneDataAsStandingData
def toStandingData {m : SharpScale} {S : ConnFamily} (d : ProductPlaneData m S) :
    PlaneStandingData m S where
  frac := d.fraction
  frac_mem := d.fraction_mem
  sigma := d.fnl
  cone := d.coneCond
  expo := d.exponent
  expo_pos := d.exponent_pos
  labelConst := d.labelBound
  boundWith_labelConst := by
    intro φ η hη α hα hsupp F hF A hA
    have h := d.productBound.le_bound η hη.1 hη.2 φ.1 φ.2 α hα hsupp F hF A hA
    have hC : labelConstants d.labelBound φ.1 = d.labelBound φ := by
      simp [labelConstants, φ.2]
    rwa [hC] at h
theorem matches_toStandingData {m : SharpScale} {S : ConnFamily} (d : ProductPlaneData m S) :
    Matches d (toStandingData d) :=
  ⟨rfl, rfl, rfl, rfl⟩
theorem existsStandingAndApertureData_holds : ExistsStandingAndApertureData := fun _ _ d =>
  ⟨⟨toStandingData d, matches_toStandingData d⟩, fun φ₀ =>
    ⟨⟨toStandingData d, φ₀⟩, matches_toStandingData d, rfl⟩⟩
end YangMills.Construction.EuclideanFunctionals.PlaneDataAsStandingData
end
