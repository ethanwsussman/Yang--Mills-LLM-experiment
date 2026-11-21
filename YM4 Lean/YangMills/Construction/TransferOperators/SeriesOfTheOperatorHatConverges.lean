import YangMills.Construction.TransferOperators.PropertiesOfMultiplicationByTheBondKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2
def HatSeriesConvergesStatement : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (β : ℝ) (S : Set J) (f : (↥S → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (d : ↥S → ℕ),
    0 < β → S.Nonempty → HasDegreeBound d f →
    ∀ F : C(J → specialUnitary, ℂ), (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
      HatSeriesProperties β S f hf d F
end YangMills.Construction.SpinHarmonics
end
