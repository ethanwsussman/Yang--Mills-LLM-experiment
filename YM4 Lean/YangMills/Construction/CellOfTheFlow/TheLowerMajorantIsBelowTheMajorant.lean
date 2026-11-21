import YangMills.Construction.CellOfTheFlow.MajorantOfAState
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps TorusFields WeightedResponses
def lowerScoreLeMajorantStatement : Prop :=
  ∀ (q : StepParameters) (T : StageTower q) (k : ℕ) (s₀ s₁ : ℝ), 0 ≤ s₀ → 0 ≤ s₁ →
    ∀ (s m : ℕ) [NeZero m] (u : MarkedSample q s m) (c : Finset (TorusSite m)),
      (∀ z, 0 ≤ lowerScore T k s₀ s₁ s m u c z ∧ lowerScore T k s₀ s₁ s m u c z ≤ siteMajorant T s₀ s₁ s m u z) ∧
        lowerScoreSum T k s₀ s₁ s m u c ≤ hullMajorantSum T s₀ s₁ s m u
end YangMills.Construction.CellWindows
end
