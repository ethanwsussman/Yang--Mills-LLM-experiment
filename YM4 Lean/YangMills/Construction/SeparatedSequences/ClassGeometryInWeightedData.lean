import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.WeightedGeometryOfClass
open SingleSequence SingleSequence.SequenceData
def Statement : Prop :=
  ∀ s : SequenceData,
    ∀ D B, s.IsWeightedTorus D B → s.WeightedGeometry B
end SeparatedClasses.WeightedGeometryOfClass
end YangMills.Construction
