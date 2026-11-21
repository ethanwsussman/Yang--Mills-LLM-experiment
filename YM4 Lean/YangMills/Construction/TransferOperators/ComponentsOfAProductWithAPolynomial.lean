import YangMills.Construction.TransferOperators.PropertiesOfMultiplicationByTheBondKernel
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def MulPullbackComponents.Statement : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (B : Set J) (f : (↥B → specialUnitary) → ℂ)
    (hf : IsRealEntryPolynomial f) (D : ↥B → ℕ)
    (s : J → HalfNatural) (ψ : C(J → specialUnitary, ℂ)),
    B.Nonempty → HasDegreeBound D f → ψ ∈ prodCoeffSpan s →
    {s' : J → HalfNatural | isotypicPartSum s'
      (toHaarL2 (mulPullback B f hf ψ : (J → specialUnitary) → ℂ)) ≠ 0}.Finite ∧
    (∀ s' : J → HalfNatural, isotypicPartSum s'
        (toHaarL2 (mulPullback B f hf ψ : (J → specialUnitary) → ℂ)) ≠ 0 →
      (∀ b, b ∉ B → s' b = s b) ∧
        IsDegreeCompatible D (restrictTo B s) (restrictTo B s')) ∧
    ∀ u, mulPullback B f hf ψ u = ∑' s' : J → HalfNatural, isotypicPartSum s'
      (toHaarL2 (mulPullback B f hf ψ : (J → specialUnitary) → ℂ)) u
end YangMills.Construction.SpinHarmonics
end
