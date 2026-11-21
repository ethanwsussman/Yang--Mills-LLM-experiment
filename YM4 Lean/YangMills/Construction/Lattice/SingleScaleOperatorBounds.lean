import YangMills.Construction.Lattice.LocalizedDecayBounds
import YangMills.Construction.Lattice.TwoScaleOperatorDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {d N : ℕ}
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
end Scales
instance decayConstantsNonempty : Nonempty DecayConstants :=
  ⟨{ base := 1
     holder := fun _ => 1
     grad := fun _ => 1
     gradHolder := fun _ _ => 1
     base_pos := one_pos
     holder_pos := fun _ _ _ => one_pos
     grad_pos := fun _ _ _ => one_pos
     gradHolder_pos := fun _ _ _ _ _ => one_pos }⟩
end YangMills.Construction.PeriodicLattice
