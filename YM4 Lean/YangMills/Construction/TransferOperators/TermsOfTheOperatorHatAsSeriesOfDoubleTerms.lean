import YangMills.Construction.TransferOperators.PropertiesOfMultiplicationByTheBondKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2
def HatTermAsDoubleSeriesStatement : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (β : ℝ) (S : Set J) (f : (↥S → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (d : ↥S → ℕ)
    (F : C(J → specialUnitary, ℂ)) (m m' : ↥S → HalfNatural),
    0 < β → S.Nonempty → HasDegreeBound d f → (F : (J → specialUnitary) → ℂ) ∈ smoothSet →
    HasSum (fun k : ↥Sᶜ → HalfNatural =>
        hatDoubleTerm β S f hf F (glue S m' k) (glue S m k))
      (hatSeriesTerm β S f hf F (m, m'))
end YangMills.Construction.SpinHarmonics
end
