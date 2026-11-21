import YangMills.Construction.HilbertSpaces.FunctionsOfAPositiveContractionAndItsSquareRoot
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.ContractionUnitary
open OneLoopNotation ComplexHilbert
def SqrtContractionProperties : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : BddOp H), IsSymmetricOp T → OpGE T 0 →
    OpLE T (idOp H) →
    (IsSymmetricOp (contractionSqrt T) ∧
      OpGE (contractionSqrt T) 0 ∧
      contractionSqrt T ^ 2 = T ∧
      (∀ ψ : H, ((‖contractionSqrt T ψ‖ ^ 2 : ℝ) : ℂ) = ⟪ψ, T ψ⟫_ℂ) ∧
      ∀ S : BddOp H, IsSymmetricOp S → OpGE S 0 → S ^ 2 = T →
        S = contractionSqrt T) ∧
    ((∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        (T' : BddOp K) (J : BddOpBetween H K),
        IsSymmetricOp T' → OpGE T' 0 → OpLE T' (idOp K) →
        J ∘L T = T' ∘L J →
        J ∘L contractionSqrt T = contractionSqrt T' ∘L J) ∧
      ∀ C : BddOp H, C * T = T * C →
        C * contractionSqrt T = contractionSqrt T * C) ∧
    linearKer (contractionSqrt T : H →ₗ[ℂ] H) = linearKer (T : H →ₗ[ℂ] H) ∧
    seqClosureOf (linearRange (contractionSqrt T : H →ₗ[ℂ] H)) =
      orthSet (linearKer (T : H →ₗ[ℂ] H))
end YangMills.Construction.ContractionUnitary
end
