import YangMills.Construction.JointSpectrum.DiscAndCone
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ConeIdentity
open YangMills.Construction.DiscGeometry Set
open scoped ComplexConjugate
def circleConj (ζ : Circle) : Circle := ζ⁻¹
theorem coe_circleConj (ζ : Circle) : (circleConj ζ : ℂ) = conj (ζ : ℂ) :=
  Circle.coe_inv_eq_conj ζ
def coneRegion : Set (unitInterval × Circle) := {p | 0 ≤ coneDefect p.1 p.2}
def ConeIdentityStatement : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ ζ : ℂ, ‖ζ‖ = 1 →
    ‖1 + (t : ℂ) * ζ‖ ^ 2 - 4 * t = (1 - t) ^ 2 - t * ‖1 - ζ‖ ^ 2) ∧
  (∀ (t : unitInterval) (ζ : Circle),
    (1 - (t : ℝ)) ^ 2 - (t : ℝ) * ‖1 - (ζ : ℂ)‖ ^ 2 = coneDefect t ζ) ∧
  (∀ (t : unitInterval) (ζ : Circle), coneDefect t (circleConj ζ) = coneDefect t ζ) ∧
  (∀ ζ : ℂ, ‖ζ‖ = 1 → ((‖1 - ζ‖ ^ 2 : ℝ) : ℂ) = 2 - ζ - conj ζ) ∧
  coneExterior = {p | coneDefect p.1 p.2 < 0} ∧
  MapsTo polarToDisc coneExterior nearRegion ∧
  coneRegion = coneExteriorᶜ ∧
  IsClosed coneRegion ∧
  ∀ p ∈ coneRegion, (p.1, circleConj p.2) ∈ coneRegion
end ConeIdentity
end YangMills.Construction
