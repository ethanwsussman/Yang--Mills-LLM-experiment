import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace SeparatedClasses
open SingleSequence SingleSequence.SequenceData
def ScalarDataOfNestedCorresponds : Prop :=
  ∀ s : SequenceData,
    ∀ 𝒮, s.IsNestedRegions 𝒮 → s.scalarData.Corresponds (scalarDataOfNested 𝒮) (s.toTorus 𝒮.side)
end SeparatedClasses
end YangMills.Construction
end
