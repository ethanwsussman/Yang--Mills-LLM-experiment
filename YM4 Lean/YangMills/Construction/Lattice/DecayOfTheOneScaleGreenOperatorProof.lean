import YangMills.Construction.Lattice.SiteIdentification
import YangMills.Construction.Lattice.TwoScaleOperatorDefs
import YangMills.Construction.LatticeFields.BlockAveraging
import YangMills.Construction.Lattice.DecayOfTheOneScaleGreenOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
private theorem blockLapConst_nonneg (d : ℕ) :
    0 ≤ LatticeFields.blockLapConst d := by
  unfold LatticeFields.blockLapConst
  positivity
abbrev _root_.YangMills.SharedProofs.p12226 := @blockLapConst_nonneg
private theorem coerciveConst_nonneg (d : ℕ) : 0 ≤ LatticeFields.coerciveConst d 1 := by
  unfold LatticeFields.coerciveConst
  refine inv_nonneg.mpr ?_
  have h1 : (0 : ℝ) ≤ LatticeFields.coerciveAuxConst d 1 := by
    unfold LatticeFields.coerciveAuxConst
    refine le_max_of_le_left ?_
    positivity
  positivity
section ViaEquiv
variable {d N M : ℕ} {κ : LatticeFields.LatticeShape d} {s : Mesh N} {ι I : Type}
end ViaEquiv
end YangMills.Construction.PeriodicLattice
