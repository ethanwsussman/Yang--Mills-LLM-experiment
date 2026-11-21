import YangMills.Construction.Towers.TheJetsOfTheFormulaOfTheRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets
def VertexTermsBounded : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
    ∀ p ∈ momentumPolydisc stripHalfWidth, ∀ μPlus μMinus : Fin 4,
      ‖vertexRemainder L k p μPlus μMinus‖ ≤ C ∧
        ‖PeriodicOperators.JetQuad.logNumber p
          (vertexConstraintJet L k p μPlus μMinus)‖ ≤ C
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets
end
