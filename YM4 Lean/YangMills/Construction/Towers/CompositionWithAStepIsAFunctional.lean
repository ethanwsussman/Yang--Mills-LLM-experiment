import YangMills.Construction.Towers.CompositionWithAStepOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.Tempered
def CompStepPreservesFunctionals : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    ∀ (F : FieldFamily L) (i : ℕ), IsLatticeFunctional L F → IsLatticeFunctional L (compStep hL i F)
end YangMills.Construction.PeriodicOperators.Tempered
end
