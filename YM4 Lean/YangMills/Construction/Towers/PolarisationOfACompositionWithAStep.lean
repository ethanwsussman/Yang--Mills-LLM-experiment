import YangMills.Construction.Towers.TheSymbolOfOneStepOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.HessianOfStepComposite
open PeriodicOperators.Tempered PeriodicOperators.Tempered.OneStep
def Claim : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    ∀ (F : FieldFamily L) (i : ℕ), IsLatticeFunctional L F → EventuallyForSides L fun n =>
      ∀ B ∈ Tower.complexEdgeForms L n 0 0, ∀ B' ∈ Tower.complexEdgeForms L n 0 0,
        complexHessian (compStep hL i F) n B B' =
          complexHessian F (n + 1) (complexStepPushforward hL n i B)
            (complexStepPushforward hL n i B')
end YangMills.Construction.Tower.HessianOfStepComposite
end
