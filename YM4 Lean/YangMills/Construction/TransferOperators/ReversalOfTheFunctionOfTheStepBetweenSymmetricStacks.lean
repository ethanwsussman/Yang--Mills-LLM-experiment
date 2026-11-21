import YangMills.Construction.TransferOperators.ObjectsOfTheStepBetweenSymmetricStacks
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory InfiniteLattice SpinHarmonics Matrices
namespace TransferOperators.CenteredStack
def ReversalStatement : Prop :=
  ∀ (μ : Fin 4) (β : ℝ), 0 < β →
    ∀ (D : CenteredStackStep μ) (f h : (D.block.links → ComplexMatrix2.specialUnitary) → ℂ)
      (hf : IsRealEntryPolynomial f) (hh : IsRealEntryPolynomial h)
      (Φ : C(D.InnerPairs → ComplexMatrix2.specialUnitary, ℂ)),
      IsRealEntryPolynomial (Φ : (D.InnerPairs → ComplexMatrix2.specialUnitary) → ℂ) →
      levelReversal D.center D.halfWidth D.vertexSet (D.transferStepFunction β hf hh Φ) =
        D.transferStepFunction β hh hf
          (levelExchanged (reflectPairPerm D.center D.halfWidth D.vertexSet) Φ)
end TransferOperators.CenteredStack
end YangMills.Construction
end
