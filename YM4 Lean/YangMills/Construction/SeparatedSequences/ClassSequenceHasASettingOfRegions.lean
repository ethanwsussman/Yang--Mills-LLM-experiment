import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.SingleSequence
open SequenceData
def ExistsNestedRegions : Prop :=
  ∀ s : SequenceData,
    ∃ R, s.IsNestedRegions R
end SeparatedClasses.SingleSequence
end YangMills.Construction
end
