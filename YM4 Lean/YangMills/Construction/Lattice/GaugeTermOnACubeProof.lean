import YangMills.Construction.Lattice.AverageTermOnACubeProof
import YangMills.Construction.Lattice.DecayOfTheOneScaleGreenOperatorProof
import YangMills.Construction.Lattice.DifferenceOperatorsCellAveragesTrees
import YangMills.Construction.Lattice.DecayingKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
private theorem blockLapConst_nonneg (d : ℕ) :
    0 ≤ LatticeFields.blockLapConst d := by apply _root_.YangMills.SharedProofs.p12226 <;> assumption
private theorem blockMomentLowerBound_pos (d : ℕ) : 0 < LatticeFields.blockMomentLowerBound d := by
  unfold LatticeFields.blockMomentLowerBound
  have := blockLapConst_nonneg d
  positivity
abbrev _root_.YangMills.SharedProofs.p223 := @blockMomentLowerBound_pos
section Norms
variable {s : Mesh N} {X ι : Type}
private theorem finset_sum_apply {α : Type} (t : Finset α) (F : α → ScaledFun d s X) (x : X) :
    (∑ i ∈ t, F i) x = ∑ i ∈ t, F i x := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]
abbrev _root_.YangMills.SharedProofs.p17632 := @finset_sum_apply
private def restrictTo (U : Set (GridPoint d s)) (g : SiteFun d s) : SiteFun d s :=
  ofMap fun x => U.indicator 1 x * g x
private theorem restrictTo_of_mem {U : Set (GridPoint d s)} (g : SiteFun d s) {x : GridPoint d s}
    (h : x ∈ U) : restrictTo U g x = g x := by
  change U.indicator 1 x * g x = g x
  rw [Set.indicator_of_mem h]
  simp
end Norms
private theorem addCircle_norm_coe_le (hN : 0 < N) (x : ℝ) : ‖(x : AddCircle (N : ℝ))‖ ≤ |x| := by apply _root_.YangMills.SharedProofs.p53979 <;> assumption
private theorem taxicabDist_nonneg (u v : Torus d N) : 0 ≤ taxicabDist u v :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _
variable {L j : ℕ}
end YangMills.Construction.PeriodicLattice
