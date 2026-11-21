import YangMills.Construction.EnergyMomentum.ChordSlopeConstant
import Mathlib
set_option autoImplicit false
open Filter Set Topology
noncomputable section
namespace YangMills.Construction
namespace EnergyMomentum
namespace ArcoshCurve
def BoundOnInterval : Prop :=
  ∀ p ∈ Icc (-Real.pi) Real.pi,
    Real.arcosh (2 - Real.cos p) = 2 * Real.arsinh |Real.sin (p / 2)| ∧
    2 * Real.arsinh |Real.sin (p / 2)| ≥ chordSlopeConstant * |p| ∧
    (2 * Real.arsinh |Real.sin (p / 2)| = chordSlopeConstant * |p| ↔ p ∈ ({0, Real.pi, -Real.pi} : Set ℝ))
def ConditionsEquiv : Prop :=
  ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p ∈ Ioc (-Real.pi) Real.pi,
    let E : ℝ := -Real.log t
    let ζ : ℂ := Complex.exp (Complex.I * (p : ℂ))
    E ∈ Ici (0 : ℝ) ∧
    ((1 - t) ^ 2 ≥ t * ‖1 - ζ‖ ^ 2 ↔ Real.sinh (E / 2) ≥ |Real.sin (p / 2)|) ∧
    (Real.sinh (E / 2) ≥ |Real.sin (p / 2)| ↔ Real.cosh E + Real.cos p ≥ 2) ∧
    (Real.cosh E + Real.cos p ≥ 2 ↔ E ≥ Real.arcosh (2 - Real.cos p)) ∧
    ((1 - t) ^ 2 ≥ t * ‖1 - ζ‖ ^ 2 → E ≥ chordSlopeConstant * |p|) ∧
    (Real.sinh (E / 2) ≥ |Real.sin (p / 2)| → E ≥ chordSlopeConstant * |p|) ∧
    (Real.cosh E + Real.cos p ≥ 2 → E ≥ chordSlopeConstant * |p|) ∧
    (E ≥ Real.arcosh (2 - Real.cos p) → E ≥ chordSlopeConstant * |p|)
def ChordEndpoints : Prop :=
  Real.arcosh 3 = 2 * Real.log (1 + Real.sqrt 2) ∧
  Real.arcosh (2 - Real.cos 0) = 0 ∧
  Real.arcosh (2 - Real.cos Real.pi) = Real.arcosh 3 ∧
  (Real.arcosh 3 - 0) / (Real.pi - 0) = chordSlopeConstant ∧
  Real.exp (-Real.arcosh 3) = (Real.sqrt 2 - 1) ^ 2 ∧
  Tendsto (fun p : ℝ => Real.arcosh (2 - Real.cos p) / |p|) (𝓝[≠] 0) (𝓝 1)
def Statement : Prop :=
  BoundOnInterval ∧ ConditionsEquiv ∧ ChordEndpoints
end ArcoshCurve
end EnergyMomentum
end YangMills.Construction
