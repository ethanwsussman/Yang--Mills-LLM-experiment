import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set TorusMetric PeriodicLattice.DirichletOperators
namespace SeparatedClasses.SingleSequence
open SequenceData
def ExistsBlockSetting : Prop :=
  ∀ s : SequenceData,
    s.L_le_blockSize → ∃ B, s.IsBlockSetting B
end SeparatedClasses.SingleSequence
end YangMills.Construction
end
