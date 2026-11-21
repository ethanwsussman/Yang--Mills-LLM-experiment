import YangMills.Construction.TransferOperators.DecayNumbersAdmissiblePairsAndTheOperatorHat
import YangMills.Construction.TransferOperators.LayersStacksTransportedVariablesAndBlocks
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.SpinHarmonics
noncomputable section
namespace YangMills.Construction.TransferOperators
variable {μ : Fin 4} {v : Set (SliceSite μ)} {I : Set (ℤ × SliceLink μ)}
def sliceGaugeMean [Finite v] (hI : ∀ i ∈ I, i.2 ∈ linksWithin v)
    (Ψ : C(I → Matrices.ComplexMatrix2.specialUnitary, ℂ))
    (u : I → Matrices.ComplexMatrix2.specialUnitary) : ℂ :=
  ∫ g, Ψ (diagonalGaugeAct hI g u) ∂Matrices.ComplexMatrix2.haarPi v
def IsLevelExchange (s : Equiv.Perm I) : Prop :=
  ∃ s₀ : ℤ → ℤ, ∀ i : I, (s i : ℤ × SliceLink μ) = (s₀ i.1.1, i.1.2)
def levelExchanged (s : Equiv.Perm I) (Ψ : C(I → Matrices.ComplexMatrix2.specialUnitary, ℂ)) :
    C(I → Matrices.ComplexMatrix2.specialUnitary, ℂ) :=
  ⟨permuteArgs s Ψ, Ψ.continuous.comp (continuous_pi fun b => continuous_apply (s b))⟩
theorem levelExchanged_apply (s : Equiv.Perm I) (Ψ : C(I → Matrices.ComplexMatrix2.specialUnitary, ℂ))
    (u : I → Matrices.ComplexMatrix2.specialUnitary) :
    levelExchanged s Ψ u = Ψ fun i => u (s i) :=
  rfl
end YangMills.Construction.TransferOperators
end
