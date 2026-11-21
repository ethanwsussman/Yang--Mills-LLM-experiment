import YangMills.Construction.SeparatedSequences.SettingsOfOneSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SeparatedClasses
open SingleSequence SingleSequence.SequenceData
def IsSeparatedOnUnitTorus : Prop :=
  ∀ s : SequenceData,
    s.L_le_blockSize → Torus.IsSeparatedChain s.data.L s.mesh s.data.blockSize s.data.gapSize s.data.t (s.regionOn s.unitTorusSide)
end YangMills.Construction.SeparatedClasses
end
