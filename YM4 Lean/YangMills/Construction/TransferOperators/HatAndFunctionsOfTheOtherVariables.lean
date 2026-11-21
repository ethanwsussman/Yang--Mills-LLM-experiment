import YangMills.Construction.TransferOperators.PropertiesOfMultiplicationByTheBondKernel
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def HatComplementMulStatement : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (β : ℝ) (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f),
    0 < β → B.Nonempty → HatCommutesComplementMul β B f hf
end YangMills.Construction.SpinHarmonics
end
