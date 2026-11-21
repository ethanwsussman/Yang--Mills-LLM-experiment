import YangMills.Construction.Lattice.AverageTermOnACubeProof
import YangMills.Construction.Lattice.DecayingKernels
import YangMills.Construction.Lattice.PointDecayingOneForms
import YangMills.Construction.Lattice.FieldNormProperties
import YangMills.Construction.Lattice.TranslationAdjointLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
namespace DecayingOneFormPairingProofs
section
variable {d N L j : ℕ}
theorem addCircle_norm_coe_le_abs (hN : 0 < N) (r : ℝ) : ‖(r : AddCircle (N : ℝ))‖ ≤ |r| := by apply _root_.YangMills.SharedProofs.p53979 <;> assumption
variable (S : Scales d L j N)
end
end DecayingOneFormPairingProofs
end YangMills.Construction.PeriodicLattice
