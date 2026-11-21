import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
def lowerHullSubsetStageHullStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (T : WeightedResponses.StageTower ℓ) (k : ℕ),
    (∀ (s m : ℕ) [NeZero m] (u : WeightedResponses.MarkedSample ℓ s m)
      (c : Finset (TorusFields.TorusSite m)),
      lowerHull T k s m u c ⊆ stageHull T s m u) ∧
    ∀ (s m : ℕ) [NeZero m] (u : WeightedResponses.MarkedSample ℓ (s + 1) m)
      (c : Finset (TorusFields.TorusSite m)),
      lowerZone T k s (StepSettings.hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
          (lowerHull T k s (m * ℓ.side) u.1 (TorusLumps.sitesInBlocks ℓ.side c)) c ⊆
        TorusLumps.storedBlocks ℓ.side (T.stage s).toStepSetup.range u.2.2.2
          (WeightedResponses.stageState T s (m * ℓ.side) u.1).2.1
          (StepSettings.hotCoreSites (T.stage s).toStepSetup u.2.2.1)
end YangMills.Construction.CellWindows
end
