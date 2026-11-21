import YangMills.Construction.TransferOperators.ConditioningOnAllBondsButOneBlockOfOneLayer
import YangMills.Construction.TransferOperators.ObjectsOfTheStepBetweenSymmetricStacks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory InfiniteLattice SpinHarmonics Matrices
namespace TransferOperators.CenteredStack
def OuterEliminationStatement : Prop :=
  ∀ (μ : Fin 4) (β : ℝ), 0 < β → ∀ ν ∈ gibbsClass (zero_lt_one (α := ℝ)) β,
    ∀ (D : CenteredStackStep μ) (f h : (D.block.links → ComplexMatrix2.specialUnitary) → ℂ)
      (hf : IsRealEntryPolynomial f) (hh : IsRealEntryPolynomial h)
      (Φ : C(D.InnerPairs → ComplexMatrix2.specialUnitary, ℂ)),
      IsRealEntryPolynomial (Φ : (D.InnerPairs → ComplexMatrix2.specialUnitary) → ℂ) →
      D.transferStepFunction β hf hh Φ ∈ smoothSet ∧
        (∀ u, (D.transferStepFunction β hf hh Φ u).im = 0) ∧
        ∫ U, f (D.enclosingStack.blockValues D.block U (D.center - D.halfWidth)) *
            h (D.enclosingStack.blockValues D.block U (D.center + D.halfWidth + 1)) *
            Φ (D.enclosingValues U) ∂ν =
          ∫ U, D.transferStepFunction β hf hh Φ (D.enclosingValues U) ∂ν
end TransferOperators.CenteredStack
end YangMills.Construction
end
