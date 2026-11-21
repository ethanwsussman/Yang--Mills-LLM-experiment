import YangMills.Construction.TransferOperators.PropertiesOfMultiplicationByTheBondKernel
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.Matrices.ComplexMatrix2
noncomputable section
namespace YangMills.Construction.SpinHarmonics
def IsotypicPartSums.Statement : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J],
    (∀ (l : J → HalfNatural) (F : HaarL2 J),
      isotypicPartSum l F ∈ prodCoeffSpan l ∧
      (isotypicPartSum l F : (J → specialUnitary) → ℂ) = isotypicPart l F ∧
      toHaarL2 (isotypicPartSum l F : (J → specialUnitary) → ℂ) = isotypicProj l F) ∧
    (∀ (l : J → HalfNatural) (H : C(J → specialUnitary, ℂ)) (u : J → specialUnitary),
      isotypicPartSum l (toHaarL2 (H : (J → specialUnitary) → ℂ)) u =
        ∫ v, isotypicKernel l u v * H v ∂haarPi J) ∧
    ∀ (l l' : J → HalfNatural) (ψ : C(J → specialUnitary, ℂ)), ψ ∈ prodCoeffSpan l →
      isotypicPartSum l (toHaarL2 (ψ : (J → specialUnitary) → ℂ)) = ψ ∧
      (l' ≠ l → isotypicPartSum l' (toHaarL2 (ψ : (J → specialUnitary) → ℂ)) = 0)
end YangMills.Construction.SpinHarmonics
end
