import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.SingleSequence
open SequenceData
def ExpansionSetAtEqLayerBonds : Prop :=
  ∀ s : SequenceData,
    ∀ n ≤ s.data.t, s.data.expansionSetAt s.Ω s.frame n = s.params.layerBondSet s.Ω s.frame n
end SeparatedClasses.SingleSequence
end YangMills.Construction
end
