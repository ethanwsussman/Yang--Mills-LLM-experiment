import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.GroundsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.MirrorOfABox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields StepSettings StepGas TorusMirror
def MirrorGroundAgrees : Prop :=
  ∀ (R : StepSetup) (n : ℕ) [NeZero n] [NeZero (4 * (R.nextRange / 4 - 2))] (V : TorusField n)
    (q : CoarseState R n) (y : TorusSite n),
    R.IsWellPosed → (hotCaseGround R V q).IsHotCase → y ∉ q.1 → q.1.Nonempty →
    IsCold R.params.threshold (mirrorField (R.nextRange / 4 - 2) y V) ∧
      GroundsAgreeNear (hotCaseGround R V q) (coldCaseGround R (mirrorField (R.nextRange / 4 - 2) y V)) y 0
        (R.nextRange / 4 - 2)
end YangMills.Construction.ResponseInTheExpansion
end
