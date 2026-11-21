import YangMills.Construction.ClusterExpansionOfAStep.EnergyNearAClass
import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.GeometryOfAKeptPart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace StepGas
open BlockAverages TorusFields TorusLumps StepSettings StepCosts StepMarks KeptRegion
variable {R : StepSetup} {n : ℕ} [NeZero n]
def GasGround.settingCore (G : GasGround R n) : SettingCore R n := ⟨G.cut, G.recordedBad⟩
structure GasGround.IsOverState (G : GasGround R n) : Prop where
  isHot : G.IsHotCase
  isCore : G.groundSetting.IsCoreOf G.settingCore
  isMarked : G.groundSetting.IsMarked G.settingCore
  field_zero : G.groundSetting.field 0 = G.groundSetting.fine
  isHull : IsHullState R.params R.range G.groundSetting.fine G.groundSetting.support
  state_eq : coarseStateOf R G.cut G.groundSetting.fine G.groundSetting.support G.groundSetting.labelling
    G.recordedBad G.groundSetting.bases = G.state
  attached_eq : attachedSites R.params.side R.range G.recordedBad G.groundSetting.support G.cut =
    clusterSites R.params.side G.recordedBad G.groundSetting.support G.cut
  bad_far : ∀ b ∈ G.recordedBad, b ∈ chartBonds R.params.side n ∧ 5 * R.ballRadius / 8 ≤
    ‖((frameDeviation R.params R.anchorRadius R.depth R.frameReach G.groundSetting.coarse G.groundSetting.fine b :
      imaginaryQuaternions) : Quaternion ℝ)‖
end StepGas
end YangMills.Construction
end
