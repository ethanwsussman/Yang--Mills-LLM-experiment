import YangMills.Construction.ReflectionPositivity.SpectralVariablesOfTheTwoPictures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.SpectralCurve
def expNegEnergy (E : ℝ) : ℝ := Real.exp (-E)
def phaseOf (u : ℝ) : ℂ := Complex.exp (Complex.I * (u : ℂ))
def AboveCurve (t : ℝ) (ζ : ℂ) : Prop :=
  (1 - t) ^ 2 ≥ t * ‖1 - ζ‖ ^ 2
def AlternativeForms (E u : ℝ) : Prop :=
  (1 - expNegEnergy E) ^ 2 - expNegEnergy E * ‖1 - phaseOf u‖ ^ 2 =
      2 * expNegEnergy E * (Real.cosh E + Real.cos u - 2) ∧
    2 * expNegEnergy E * (Real.cosh E + Real.cos u - 2) =
      4 * expNegEnergy E * (Real.sinh (E / 2) ^ 2 - Real.sin (u / 2) ^ 2)
def PowersStayAbove (E u : ℝ) (k : ℕ) : Prop :=
  AboveCurve (expNegEnergy E) (phaseOf u) →
    AboveCurve (expNegEnergy E ^ k) (phaseOf u ^ k)
def AboveCone (E u : ℝ) : Prop :=
  AboveCurve (expNegEnergy E) (phaseOf u) → |u| ≤ Real.pi →
    E ≥ 2 * Real.arsinh |Real.sin (u / 2)| ∧
      2 * Real.arsinh |Real.sin (u / 2)| ≥ slopeConstant * |u| ∧
      (E = 0 → u = 0)
def CurveFacts : Prop :=
  ∀ (E u : ℝ) (k : ℕ), 0 ≤ E → 1 ≤ k →
    AlternativeForms E u ∧ PowersStayAbove E u k ∧ AboveCone E u
end YangMills.Construction.ReflectionPositivity.DirectionPictures.SpectralCurve
