import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2
def PartialCoeffL2Properties : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (B : Set J), B.Nonempty → B ≠ Set.univ →
    (∀ (γ : PeterWeylIndex ↥Bᶜ) (F : HaarL2 J),
      MemLp (partialCoeff B γ F) 2 (haarPi ↥B)) ∧
    (∀ γ : PeterWeylIndex ↥Bᶜ, ∃ P : HaarL2 J →L[ℂ] HaarL2 ↥B,
      ∀ F, P F = toHaarL2 (partialCoeff B γ F)) ∧
    ∀ F : HaarL2 J,
      HasSum (fun γ : PeterWeylIndex ↥Bᶜ => ‖toHaarL2 (partialCoeff B γ F)‖ ^ 2) (‖F‖ ^ 2)
end YangMills.Construction.SpinHarmonics
end
