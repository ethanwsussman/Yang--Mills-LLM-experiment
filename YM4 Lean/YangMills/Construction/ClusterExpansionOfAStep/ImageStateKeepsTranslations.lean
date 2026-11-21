import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.FramesOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open TorusLumps TorusFields StepSettings
def CoarseWeightExpansionTranslationInvariant : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → R.ColdChainFits → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
    ∀ (V : TorusField n) (Y : Finset (TorusSite n)) (ω : Y → CoarseLabel R.labels.Ω R.params.side) (u : TorusSite n),
      IsBlockTranslation R.params u → IsHullState R.params R.nextRange V Y →
      coarseWeightExpansion R n (TorusFields.translate u V) (translateSet u Y) (translateLabel u Y ω) = coarseWeightExpansion R n V Y ω
end ClusterExpansionOfAStep
end YangMills.Construction
end
