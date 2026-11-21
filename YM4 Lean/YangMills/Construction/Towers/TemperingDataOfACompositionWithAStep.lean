import YangMills.Construction.Towers.TheSymbolOfOneStepOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.TemperedComposition
open PeriodicOperators.Tempered PeriodicOperators.Tempered.OneStep
def CompStepTemperedWitnessExists : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    ∀ (F : FieldFamily L) (δ : ℝ) (σ : SymbolArray) (w : ℕ → ℝ) (i : ℕ),
      IsLatticeFunctional L F → IsTemperedWitness L F δ σ w →
        ∃ δ' C : ℝ, IsTemperedWitness L (compStep hL i F) δ'
          (stepSymbolArray L i σ) fun n => C * w (n + 1)
end YangMills.Construction.Tower.TemperedComposition
end
