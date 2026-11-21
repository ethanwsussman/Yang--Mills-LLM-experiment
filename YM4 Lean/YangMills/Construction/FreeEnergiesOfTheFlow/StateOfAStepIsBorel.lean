import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace FreeEnergiesOfTheFlow
open TorusLumps StepSettings WeightedResponses
def MeasurableNextStageState : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (T : StageTower ℓ) (s n : ℕ) [NeZero n],
    Measurable fun p : StageState T s (n * ℓ.side) × StepOutcome ℓ n =>
      ((p.2.2.1, coarseStateOf (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup p.2.2.1) p.1.1 p.1.2.1
          p.1.2.2 p.2.2.2 p.2.1) :
        StageState T (s + 1) n)
end FreeEnergiesOfTheFlow
end YangMills.Construction
end
