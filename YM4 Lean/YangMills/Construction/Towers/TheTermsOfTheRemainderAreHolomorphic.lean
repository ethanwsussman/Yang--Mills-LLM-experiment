import YangMills.Construction.ComplexAnalysis.PartialDerivativesAndLogarithm
import YangMills.Construction.Towers.TheJetsOfTheFormulaOfTheRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.TermsHolomorphic
open PeriodicOperators.JetQuad
def RemainderTermsHolomorphic : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k → ∀ μPlus μMinus : Fin 4,
    ComplexVariables.IsHolomorphicScalar (openPolydisc stripHalfWidth)
        (fun p => edgeRemainder L k p μPlus μMinus) ∧
      ComplexVariables.IsHolomorphicScalar (openPolydisc stripHalfWidth)
        (fun p => vertexRemainder L k p μPlus μMinus) ∧
      ComplexVariables.IsHolomorphicScalar (openPolydisc stripHalfWidth)
        (fun p => logNumber p (edgeConstraintJet L k p μPlus μMinus)) ∧
      ComplexVariables.IsHolomorphicScalar (openPolydisc stripHalfWidth)
        (fun p => logNumber p (vertexConstraintJet L k p μPlus μMinus))
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.TermsHolomorphic
end
