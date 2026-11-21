import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedClasses
open SingleSequence SingleSequence.SequenceData
def ExistsGaugeSetting : Prop :=
  ∀ s : SequenceData,
    ∃ W, s.IsGaugeSetting W
end YangMills.Construction.SeparatedClasses
end
