import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedClasses
def UnitMassWeightsStatement : Prop :=
  ∀ s : SingleSequence.SequenceData,
    s.WeightsAtUnitMass
end YangMills.Construction.SeparatedClasses
end
