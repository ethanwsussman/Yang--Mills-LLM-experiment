import YangMills.Construction.TransferOperators.TwistedActionOnAPowerOfG
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransferOperators
open MeasureTheory SpinHarmonics
namespace TwistedActionOperators
def Statement : Prop :=
  ∀ (J V : Type) [Finite J] [Nonempty J] (t h : J → V),
    (∀ g : V → Matrices.ComplexMatrix2.specialUnitary, ∃ T, IsTwistedTranslation t h g T) ∧
    ∀ ρ : (V → Matrices.ComplexMatrix2.specialUnitary) → HaarL2 J →L[ℂ] HaarL2 J,
      (∀ g, IsTwistedTranslation t h g (ρ g)) →
      (∀ g, Function.Bijective (ρ g)) ∧
      (∀ g (φ ψ : HaarL2 J), inner ℂ (ρ g φ) (ρ g ψ) = inner ℂ φ ψ) ∧
      (∀ g g', ρ g * ρ g' = ρ (g * g')) ∧
      ρ 1 = 1 ∧
      ∀ A : (J → Matrices.ComplexMatrix2.specialUnitary) ×
          (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ, Continuous A →
        (∀ (g : V → Matrices.ComplexMatrix2.specialUnitary)
          (u u' : J → Matrices.ComplexMatrix2.specialUnitary),
          A (twistedConjAction t h g u, twistedConjAction t h g u') = A (u, u')) →
        ∀ g, Schatten.kernelOp (Matrices.ComplexMatrix2.haarPi J) A * ρ g =
          ρ g * Schatten.kernelOp (Matrices.ComplexMatrix2.haarPi J) A
end TwistedActionOperators
end YangMills.Construction.TransferOperators
end
