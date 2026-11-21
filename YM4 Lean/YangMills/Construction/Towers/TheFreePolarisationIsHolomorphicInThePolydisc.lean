import YangMills.Construction.ComplexAnalysis.PartialDerivativesAndLogarithm
import YangMills.Construction.Towers.TheJetsOfTheFormulaOfTheRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets
def FreePolarizationHolomorphic : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ μPlus μMinus : Fin 4,
      ComplexVariables.IsHolomorphicScalar (openPolydisc stripHalfWidth)
        (freePolarizationEntry L k hL μPlus μMinus)
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets
end
