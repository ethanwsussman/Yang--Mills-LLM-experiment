import YangMills.Construction.Towers.TheJetsOfTheFormulaOfTheRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.UnconstrainedDeterminants
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
def PolarizationLogDetFormula : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    IsJointInvertibilityWidth L k hL stripHalfWidth ∧
      ∀ p ∈ momentumPolydisc stripHalfWidth, ∀ μPlus μMinus : Fin 4,
        freePolarizationEntry L k hL μPlus μMinus p =
          -(1 / 2) * logNumber p (edgeMiddleJet L k p μPlus μMinus) -
              1 / 2 * logNumber p (edgeConstraintJet L k p μPlus μMinus) +
            logNumber p (vertexMiddleJet L k p μPlus μMinus) +
          logNumber p (vertexConstraintJet L k p μPlus μMinus)
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.UnconstrainedDeterminants
end
