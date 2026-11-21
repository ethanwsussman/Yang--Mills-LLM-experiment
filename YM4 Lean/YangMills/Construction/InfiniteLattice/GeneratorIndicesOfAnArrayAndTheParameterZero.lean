import YangMills.Construction.InfiniteLattice.ToriOfAnyShapeArraysAndPerturbedMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice.LocalObservableArray
variable (A : LocalObservableArray)
def untiltedTorusPartition (Γ : PeriodSublattice 1) (β : ℝ) : ℝ := A.tiltedPartition Γ β 0
end YangMills.Construction.InfiniteLattice.LocalObservableArray
