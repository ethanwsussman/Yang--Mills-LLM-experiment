import YangMills.Construction.TransferOperators.CubicToriAndProductsOfOperatorsOnPowersOfG
import YangMills.Construction.TransferOperators.TwistedActionOnAPowerOfG
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TransferOperators
open SpinHarmonics
def TwistedAverageStatement : Prop :=
  ∀ (J V : Type) [Finite J] [Nonempty J] [Finite V] [Nonempty V] (s r : J → V),
    (∃ T, IsTwistedAverage s r T) ∧
    ∀ (ρ : (V → Matrices.ComplexMatrix2.specialUnitary) → HaarL2 J →L[ℂ] HaarL2 J)
      (Q : HaarL2 J →L[ℂ] HaarL2 J),
      (∀ g, IsTwistedTranslation s r g (ρ g)) → IsTwistedAverage s r Q →
      (∀ ψ φ : HaarL2 J,
        Integrable (fun g : V → Matrices.ComplexMatrix2.specialUnitary => inner ℂ ψ (ρ g φ))
          (Matrices.ComplexMatrix2.haarPi V)) ∧
      (∀ ψ φ : HaarL2 J,
        inner ℂ ψ (Q φ) = ∫ g : V → Matrices.ComplexMatrix2.specialUnitary, inner ℂ ψ (ρ g φ)
          ∂Matrices.ComplexMatrix2.haarPi V) ∧
      IsSymmetricOp Q ∧
      Q * Q = Q ∧
      Set.range Q = {φ | ∀ g, ρ g φ = φ} ∧
      ∀ A : HaarL2 J →L[ℂ] HaarL2 J, IsSymmetricOp A →
        (∀ g, A * ρ g = ρ g * A) → A * Q = Q * A
end YangMills.Construction.TransferOperators
end
