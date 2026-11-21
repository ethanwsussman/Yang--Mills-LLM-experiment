import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
open StepCosts TorusFields TorusLumps
open Classical in
def ChartBondCountPerBlock : Prop :=
  ∀ (L n : ℕ) [NeZero L] [NeZero n], Odd L → 2 ≤ n → ∀ Y : TorusSite n,
    ((chartBonds L n).filter fun b => parentBlock L b.1 = Y).card = chartBondCount L
end YangMills.Construction.StepSettings
end
