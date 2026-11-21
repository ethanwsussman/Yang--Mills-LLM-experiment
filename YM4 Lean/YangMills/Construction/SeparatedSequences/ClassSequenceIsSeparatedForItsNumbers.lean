import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedClasses
open SingleSequence SingleSequence.SequenceData
def IsSeparatedForOwnParameters : Prop :=
  ∀ s : SequenceData,
    (s.Ω 0).Nonempty ∧ SeparatedSequences.IsSeparatedSequence s.data.scales (s.data.gapSize : ℝ) s.Ω
end YangMills.Construction.SeparatedClasses
end
