import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.ReflectionPositiveLimits.LAdicNumbersAndLAdicMirrors
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.ReflectionPositiveLimits.SinhSineInequality
def SinhDominatesAbsSin (E q t : ℝ) : Prop :=
  Real.sinh (t * E / 2) ≥ |Real.sin (t * q / 2)|
def SinhDominatesAbsSinIffStatement : Prop :=
  ∀ (L : ℕ), YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L → ∀ (E q : ℝ), 0 ≤ E →
    ((∀ t ∈ YangMills.Construction.ReflectionPositivity.posAdicGridPoints L,
        SinhDominatesAbsSin E q t) ↔ E ≥ |q|) ∧
    (∀ S : Set ℝ, S ⊆ Set.Ioi 0 → AccPt (0 : ℝ) (𝓟 S) →
      (∀ t ∈ S, SinhDominatesAbsSin E q t) → E ≥ |q|) ∧
    (E ≥ |q| → ∀ t : ℝ, 0 < t →
      Real.sinh (t * E / 2) ≥ t * E / 2 ∧ t * E / 2 ≥ t * |q| / 2 ∧
        t * |q| / 2 ≥ |Real.sin (t * q / 2)|)
end YangMills.Construction.ReflectionPositiveLimits.SinhSineInequality
