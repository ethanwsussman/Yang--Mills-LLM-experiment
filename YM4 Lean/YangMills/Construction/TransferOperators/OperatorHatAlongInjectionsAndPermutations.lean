import YangMills.Construction.TransferOperators.PropertiesOfMultiplicationByTheBondKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2
def HatNaturalityStatement : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (β : ℝ) (S : Set J) (f : (↥S → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f),
    0 < β → S.Nonempty → HatNaturalInjective β S f hf ∧ HatEquivariantPerm β S f hf
end YangMills.Construction.SpinHarmonics
end
