import YangMills.Construction.JointSpectrum.CommutingFamilies
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open JointSpectrum
namespace DiscGeometry
def closedUnitDisc : Set ℂ := {z | ‖z‖ ≤ 1}
def polarToDisc (p : unitInterval × Circle) : ℂ := ((p.1 : ℝ) : ℂ) * (p.2 : ℂ)
theorem polarToDisc_mem_closedUnitDisc (p : unitInterval × Circle) :
    polarToDisc p ∈ closedUnitDisc := by
  have hnonneg : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2.1
  have hle : (p.1 : ℝ) ≤ 1 := p.1.2.2
  simpa [closedUnitDisc, polarToDisc, abs_of_nonneg hnonneg, Circle.norm_coe] using hle
def nearRegion : Set ℂ := {z | z ∈ closedUnitDisc ∧ ‖1 + z‖ ^ 2 < 4 * ‖z‖}
def coneDefect (t : unitInterval) (ζ : Circle) : ℝ :=
  (1 - (t : ℝ)) ^ 2 - (t : ℝ) * ‖1 - (ζ : ℂ)‖ ^ 2
def coneExterior : Set (unitInterval × Circle) :=
  {p | 0 < (p.1 : ℝ) ∧ (1 - (p.1 : ℝ)) ^ 2 < (p.1 : ℝ) * ‖1 - (p.2 : ℂ)‖ ^ 2}
def coneExteriorOf (J : Type*) [Unique J] : Set (SpectralDomain J) :=
  {p | (p.1, p.2 default) ∈ coneExterior}
end DiscGeometry
end YangMills.Construction
