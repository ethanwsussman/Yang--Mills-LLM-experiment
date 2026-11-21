import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedClasses
open SingleSequence SingleSequence.SequenceData
def ScalarDataOfBlockSettingCorresponds : Prop :=
  ∀ s : SequenceData,
    ∀ 𝒮, s.IsBlockSetting 𝒮 → s.scalarData.Corresponds (scalarDataOfBlockSetting 𝒮) (s.toTorus s.unitTorusSide)
end YangMills.Construction.SeparatedClasses
end
