import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses
namespace NestedProjectionsOfClass
open SingleSequence SingleSequence.SequenceData
def Statement : Prop :=
  ∀ s : SequenceData,
    ∀ 𝒮, s.IsNestedRegions 𝒮 → s.NestedProjections 𝒮
end NestedProjectionsOfClass
end SeparatedClasses
end YangMills.Construction
