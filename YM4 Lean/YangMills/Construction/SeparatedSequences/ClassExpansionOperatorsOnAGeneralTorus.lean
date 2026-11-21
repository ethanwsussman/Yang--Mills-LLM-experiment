import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.GaugeCoarseOperatorsOfClass
open SingleSequence SingleSequence.SequenceData
def Statement : Prop :=
  ∀ s : SequenceData,
    ∀ W, s.IsGaugeSetting W → s.GaugeCoarseOperators W
end SeparatedClasses.GaugeCoarseOperatorsOfClass
end YangMills.Construction
