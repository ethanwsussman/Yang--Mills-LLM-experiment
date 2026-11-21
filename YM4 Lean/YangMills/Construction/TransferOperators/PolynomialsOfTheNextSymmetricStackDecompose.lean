import YangMills.Construction.TransferOperators.ObjectsOfTheStepBetweenSymmetricStacks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory InfiniteLattice SpinHarmonics Matrices
namespace TransferOperators.CenteredStack
def PolynomialSplitStatement : Prop :=
  ∀ (μ : Fin 4) (D : CenteredStackStep μ) (v₀ : Set (SliceSite μ)) [Finite v₀],
    v₀ ⊆ D.vertexSet → (D.block.links : Set (SliceLink μ)) = linksWithin v₀ →
    ∀ Ψ : (centeredLinkPairs D.center (D.halfWidth + 1) v₀ → ComplexMatrix2.specialUnitary) → ℂ,
      IsRealEntryPolynomial Ψ →
      ∃ (m : ℕ) (f h : Fin m → (D.block.links → ComplexMatrix2.specialUnitary) → ℂ)
        (Φ : Fin m → C(D.InnerPairs → ComplexMatrix2.specialUnitary, ℂ)),
        (∀ α, IsRealEntryPolynomial (f α)) ∧ (∀ α, IsRealEntryPolynomial (h α)) ∧
        (∀ α, IsRealEntryPolynomial (Φ α : (D.InnerPairs → ComplexMatrix2.specialUnitary) → ℂ)) ∧
        ∀ w : ℤ × SliceLink μ → ComplexMatrix2.specialUnitary, Ψ (fun p => w p.1) =
          ∑ α, f α (fun b => w (D.center - D.halfWidth, b.1)) *
            h α (fun b => w (D.center + D.halfWidth + 1, b.1)) * Φ α (fun p => w p.1)
end TransferOperators.CenteredStack
end YangMills.Construction
end
