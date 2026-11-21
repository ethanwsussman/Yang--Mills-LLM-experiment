import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.FramesOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open BlockAverages TorusLumps TorusFields StepSettings
def CoarseWeightExpansionGaugeInvariant : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → R.ColdChainFits → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
    ∀ (V : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side)
      (g : TorusSite n → UnitQuaternion),
      IsHullState R.params R.nextRange V Y →
      coarseWeightExpansion R n (gaugeTransform g V) Y (coarseGaugeAct (R := R) Y g ω) = coarseWeightExpansion R n V Y ω
end ClusterExpansionOfAStep
end YangMills.Construction
end
