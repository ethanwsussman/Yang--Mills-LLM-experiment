import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.NestedGeometryOfClass
open SingleSequence SingleSequence.SequenceData
def Statement : Prop :=
  ∀ s : SequenceData,
    ∀ 𝒮, s.IsNestedRegions 𝒮 → s.NestedGeometry 𝒮
end SeparatedClasses.NestedGeometryOfClass
end YangMills.Construction
