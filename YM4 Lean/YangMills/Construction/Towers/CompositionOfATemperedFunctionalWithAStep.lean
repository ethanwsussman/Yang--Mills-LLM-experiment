import YangMills.Construction.OneLoopLaw.CoefficientOfAFunctional
import YangMills.Construction.Towers.CompositionWithAStepOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TemperedComposition
open PeriodicOperators.Tempered
def TemperedCompStep : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    ∀ (F : FieldFamily L) (i : ℕ), IsTemperedFunctional L F →
      IsTemperedFunctional L (compStep hL i F) ∧
        OneLoopLaw.FunctionalStiffness.stiffnessConstant hL (compStep hL i F) =
          OneLoopLaw.FunctionalStiffness.stiffnessConstant hL F
end YangMills.Construction.TemperedComposition
end
