import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction
namespace LimitForms
def symbolKernelDecayStatement : Prop :=
  ∀ (m : ℤ) (bound : ℕ → ℝ), -4 < m → ∃ C : ℝ, ∀ (a : (Fin 4 → ℝ) → ℂ) (w : Fin 4 → ℝ),
    (∀ (i : Fin 4) (p : Fin 4 → ℝ), a (p + Pi.single i (2 * Real.pi)) *
      Complex.exp (Complex.I * ((2 * Real.pi * w i : ℝ) : ℂ)) = a p) →
    (∀ (j : ℕ) (p : Fin 4 → ℝ), p ∈ brillouinBox → p ≠ 0 → ContDiffAt ℝ j a p) →
    (∀ (l : Fin 4) (j : ℕ) (p : Fin 4 → ℝ), p ∈ brillouinBox → p ≠ 0 →
      ‖iteratedDeriv j (fun t : ℝ => a (Function.update p l t)) (p l)‖ ≤
        bound j * Real.sqrt (momentumNormSq p) ^ (m - (j : ℤ))) →
    ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4 * ∫ p in brillouinBox, a p *
        Complex.exp (Complex.I * ((∑ l, p l * w l : ℝ) : ℂ))‖ ≤
      C * (1 + Real.sqrt (∑ l, w l ^ 2)) ^ (-4 - m)
end LimitForms
end YangMills.Construction
end
