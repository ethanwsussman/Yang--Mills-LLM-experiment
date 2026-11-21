import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.GaugeProjectionOfClass
open SingleSequence SingleSequence.SequenceData
def Statement : Prop :=
  ∀ s : SequenceData,
    ∀ W, s.IsGaugeSetting W → s.GaugeProjection W
end SeparatedClasses.GaugeProjectionOfClass
end YangMills.Construction
