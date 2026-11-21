import YangMills.Construction.Matrices.FunctionsAndOperatorsOfSeveralVariablesOnG
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def TensorFnMemL2Inner : Prop :=
  ∀ (J : Type) [Finite J] (B : Set J)
    (f f' : (↥B → Matrices.ComplexMatrix2.specialUnitary) → ℂ)
    (h h' : (↥Bᶜ → Matrices.ComplexMatrix2.specialUnitary) → ℂ),
    MemLp f 2 (Matrices.ComplexMatrix2.haarPi ↥B) → MemLp f' 2 (Matrices.ComplexMatrix2.haarPi ↥B) →
    MemLp h 2 (Matrices.ComplexMatrix2.haarPi ↥Bᶜ) → MemLp h' 2 (Matrices.ComplexMatrix2.haarPi ↥Bᶜ) →
      MemLp (tensorFn B f h) 2 (Matrices.ComplexMatrix2.haarPi J) ∧
      (inner ℂ (toHaarL2 (tensorFn B f h)) (toHaarL2 (tensorFn B f' h')) : ℂ) =
        inner ℂ (toHaarL2 f) (toHaarL2 f') * inner ℂ (toHaarL2 h) (toHaarL2 h')
end YangMills.Construction.SpinHarmonics
end
