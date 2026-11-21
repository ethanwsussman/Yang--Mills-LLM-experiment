import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace SeparatedClasses
open SingleSequence SingleSequence.SequenceData
def NestedMassFormHolds : Prop :=
  ∀ s : SequenceData,
    ∀ 𝒮, s.IsNestedRegions 𝒮 → s.NestedMassForm 𝒮
end SeparatedClasses
end YangMills.Construction
end
