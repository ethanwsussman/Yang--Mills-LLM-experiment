import YangMills.Construction.Lattice.LocalizedDecayBounds
import YangMills.Construction.Lattice.TwoScaleOperatorDefs
import YangMills.Construction.LatticeFields.CompressedGreenBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {d N : ℕ}
def MultiField.indicatorMul {s : Mesh N} {ι : Type} (U : Set (GridPoint d s))
    (f : MultiField d s ι) : MultiField d s ι :=
  MultiField.mulLeft (ScaledFun.ofMap (U.indicator 1)) f
end YangMills.Construction.PeriodicLattice
