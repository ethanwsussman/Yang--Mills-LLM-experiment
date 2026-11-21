import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedClasses
open SingleSequence SingleSequence.SequenceData
def ScalarDataOfWeightedCorresponds : Prop :=
  ∀ s : SequenceData,
    ∀ D B, s.IsWeightedTorus D B → s.scalarData.Corresponds (scalarDataOfWeighted B) (s.toTorus D.side)
end YangMills.Construction.SeparatedClasses
end
