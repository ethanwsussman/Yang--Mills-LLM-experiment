import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses.SingleSequence
def NestedAnchorsOfClass : Prop :=
  ∀ s : SequenceData,
    ∀ 𝒮, s.IsNestedRegions 𝒮 → s.NestedAnchors 𝒮
end YangMills.Construction.SeparatedClasses.SingleSequence
end
