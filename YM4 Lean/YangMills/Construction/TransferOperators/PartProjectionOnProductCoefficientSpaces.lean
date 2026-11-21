import YangMills.Construction.TransferOperators.DecayNumbersAdmissiblePairsAndTheOperatorHat
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SpinHarmonics
open MeasureTheory Matrices.ComplexMatrix2
def PartProjOnProdCoeffSpanStatement : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (S : Set J) (spins : J → HalfNatural)
    (ψ : C(J → specialUnitary, ℂ)) (m : ↥S → HalfNatural),
    S.Nonempty → ψ ∈ prodCoeffSpan spins →
    (m = restrictTo S spins → partIsotypicProjC S m ψ = ψ) ∧
    (m ≠ restrictTo S spins → partIsotypicProjC S m ψ = 0)
end YangMills.Construction.SpinHarmonics
end
