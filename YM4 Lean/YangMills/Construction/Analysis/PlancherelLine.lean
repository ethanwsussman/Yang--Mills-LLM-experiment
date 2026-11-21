import Mathlib
open MeasureTheory
set_option autoImplicit false
namespace YangMills.Construction.Analysis
def PlancherelRealLine : Prop :=
  ∀ u : ℝ → ℂ, Continuous u → HasCompactSupport u →
    Integrable (fun ξ : ℝ => ‖∫ t : ℝ, u t * Complex.exp (Complex.I * t * ξ)‖ ^ 2) ∧
      ∫ t : ℝ, ‖u t‖ ^ 2 =
        (2 * Real.pi)⁻¹ * ∫ ξ : ℝ, ‖∫ t : ℝ, u t * Complex.exp (Complex.I * t * ξ)‖ ^ 2
end YangMills.Construction.Analysis
