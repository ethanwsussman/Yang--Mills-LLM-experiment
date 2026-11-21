import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace YangMills.Construction
namespace LimitForms
def latticeSine (p : Fin 4 → ℝ) (l : Fin 4) : ℝ := 2 * Real.sin (p l / 2)
def latticeSineNormSq (p : Fin 4 → ℝ) : ℝ := ∑ l, latticeSine p l ^ 2
def planeSineVector (p : Fin 4 → ℝ) (μ ν i : Fin 4) : ℝ :=
  (if i = μ then latticeSine p ν else 0) - (if i = ν then latticeSine p μ else 0)
def plaquetteBarycentreShift (z : Fin 4 → ℤ) (μ ν α β l : Fin 4) : ℝ :=
  (z l : ℝ) + ((if l = μ then 1 / 2 else 0) + (if l = ν then 1 / 2 else 0) -
    (if l = α then 1 / 2 else 0) - (if l = β then 1 / 2 else 0))
def fourierKernelAt (a : (Fin 4 → ℝ) → ℂ) (w : Fin 4 → ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ ^ 4 * ∫ p in brillouinBox, a p * Complex.exp (Complex.I * ((∑ l, p l * w l : ℝ) : ℂ))
def curlProjectionSymbol (μ ν α β : Fin 4) (p : Fin 4 → ℝ) : ℂ :=
  (((∑ i, planeSineVector p μ ν i * planeSineVector p α β i) / latticeSineNormSq p : ℝ) : ℂ)
def curlProjectionKernelStatement : Prop :=
  ∃ C : ℝ, ∀ (z : Fin 4 → ℤ) (μ ν α β : Fin 4), μ < ν → α < β → z ≠ 0 →
    ‖fourierKernelAt (curlProjectionSymbol μ ν α β) (plaquetteBarycentreShift z μ ν α β) - (maxwellKernel z μ ν α β : ℂ)‖ ≤
      C * ((1 + Real.sqrt (intNormSq z)) ^ 5)⁻¹
end LimitForms
end YangMills.Construction
end
