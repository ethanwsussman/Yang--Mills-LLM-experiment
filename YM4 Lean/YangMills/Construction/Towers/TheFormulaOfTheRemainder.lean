import YangMills.Construction.Towers.TheJetsOfTheFormulaOfTheRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.Formula
def RemainderFormula : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ p ∈ momentumPolydisc stripHalfWidth, ∀ μPlus μMinus : Fin 4,
      freePolarizationEntry L k hL μPlus μMinus p - massiveLogFnSharp L k p μPlus μMinus =
        -(1 / 2) * edgeRemainder L k p μPlus μMinus +
              vertexRemainder L k p μPlus μMinus -
            1 / 2 * PeriodicOperators.JetQuad.logNumber p (edgeConstraintJet L k p μPlus μMinus) +
          PeriodicOperators.JetQuad.logNumber p (vertexConstraintJet L k p μPlus μMinus)
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.Formula
end
