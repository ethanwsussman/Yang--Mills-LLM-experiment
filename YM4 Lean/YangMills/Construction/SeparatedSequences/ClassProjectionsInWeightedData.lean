import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.WeightedProjectionsOfClass
open SingleSequence SingleSequence.SequenceData
def Statement : Prop :=
  ∀ s : SequenceData,
    ∀ D B, s.IsWeightedTorus D B → s.WeightedProjections B
end SeparatedClasses.WeightedProjectionsOfClass
end YangMills.Construction
