import YangMills.Construction.TransferOperators.CubicToriAndProductsOfOperatorsOnPowersOfG
import YangMills.Construction.TransferOperators.TwistedActionOnAPowerOfG
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.TransferOperators
open SpinHarmonics
def IsMultiplicationOp {J : Type} [Countable J]
    (w : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ)
    (T : HaarL2 J →L[ℂ] HaarL2 J) : Prop :=
  ∀ φ : HaarL2 J, (T φ : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ)
    =ᵐ[Matrices.ComplexMatrix2.haarPi J]
      fun u => w u * (φ : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ) u
def BoundedMultiplicationStatement : Prop :=
  ∀ (J : Type) [Finite J] [Nonempty J] (w : (J → Matrices.ComplexMatrix2.specialUnitary) → ℂ),
    Continuous w →
    (∀ u, (w u).im = 0 ∧ 0 ≤ (w u).re ∧ (w u).re ≤ 1) →
    (∃ T, IsMultiplicationOp w T) ∧
    ∀ T, IsMultiplicationOp w T →
      IsPositiveOp T ∧ OpLE T 1 ∧ ‖T‖ ≤ 1 ∧
      ∀ (V : Type) (s r : J → V) (g : V → Matrices.ComplexMatrix2.specialUnitary)
        (R : HaarL2 J →L[ℂ] HaarL2 J),
        IsTwistedTranslation s r g R →
        (∀ u, w (twistedConjAction s r g⁻¹ u) = w u) → T * R = R * T
end YangMills.Construction.TransferOperators
end
