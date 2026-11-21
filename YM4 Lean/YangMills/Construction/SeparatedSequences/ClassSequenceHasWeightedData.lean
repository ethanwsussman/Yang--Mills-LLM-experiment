import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedClasses
open SingleSequence SingleSequence.SequenceData
def ExistsWeightedTorus : Prop :=
  ∀ s : SequenceData,
    s.L_le_blockSize → ∃ D B, s.IsWeightedTorus D B
end YangMills.Construction.SeparatedClasses
end
