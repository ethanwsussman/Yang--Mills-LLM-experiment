import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.BlockGeometryOfClass
open SingleSequence SingleSequence.SequenceData
def Statement : Prop :=
  ∀ s : SequenceData,
    ∀ 𝒮, s.IsBlockSetting 𝒮 → s.BlockSettingGeometry 𝒮
end SeparatedClasses.BlockGeometryOfClass
end YangMills.Construction
