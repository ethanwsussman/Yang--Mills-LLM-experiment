import YangMills.Construction.Lattice.GreenOperatorsOfCubesInLevelUnitsProof
import YangMills.Construction.Lattice.NormInequalitiesOfTheOneScaleGreenOperatorProof
import YangMills.Construction.Lattice.OneScaleOperatorBounds
import YangMills.Construction.Lattice.SingleScaleInverseDecay
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
namespace CenteredCubeDecay
theorem taxicabDist_triangle (u v w : Torus d N) :
    taxicabDist u w ≤ taxicabDist u v + taxicabDist v w := by
  unfold taxicabDist
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun μ _ => ?_
  have h := norm_add_le (u μ - v μ) (v μ - w μ)
  rwa [sub_add_sub_cancel] at h
theorem taxicabDist_comm (u v : Torus d N) : taxicabDist u v = taxicabDist v u := by apply _root_.YangMills.SharedProofs.p1021 <;> assumption
theorem taxicabDist_self (u : Torus d N) : taxicabDist u u = 0 := by
  simp [taxicabDist]
theorem taxicabDist_le_of_maxDist_le_one {u v : Torus d N} (hle : maxDist u v ≤ 1) :
    taxicabDist u v ≤ d := by
  unfold taxicabDist
  calc ∑ μ, ‖u μ - v μ‖ ≤ ∑ _μ : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum fun μ _ => (norm_le_pi_norm (u - v) μ).trans hle
    _ = d := by simp
section Seminorms
variable {s : Mesh N} {ι : Type}
theorem siteFun_holderSemi_nonneg (α : ℝ) (f : SiteFun d s) :
    0 ≤ SiteFun.holderSemi α f := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.siteFun_holderSemi_nonneg <;> assumption
theorem multiField_holderSemi_nonneg [Fintype ι] (α : ℝ) (f : MultiField d s ι) :
    0 ≤ MultiField.holderSemi α f := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.multiField_holderSemi_nonneg <;> assumption
theorem siteFun_maxNorm_nonneg (f : SiteFun d s) : 0 ≤ SiteFun.maxNorm f :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem abs_le_siteFun_maxNorm (f : SiteFun d s) (x : GridPoint d s) :
    |f x| ≤ SiteFun.maxNorm f :=
  le_ciSup (f := fun x => |f x|) (Set.finite_range _).bddAbove x
theorem multiField_normAt_nonneg [Fintype ι] (f : MultiField d s ι) (x : GridPoint d s) :
    0 ≤ MultiField.normAt f x :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem multiField_maxNorm_nonneg [Fintype ι] (f : MultiField d s ι) :
    0 ≤ MultiField.maxNorm f :=
  Real.iSup_nonneg fun _ => multiField_normAt_nonneg f _
theorem abs_le_normAt [Fintype ι] (f : MultiField d s ι) (x : GridPoint d s) (i : ι) :
    |f (i, x)| ≤ MultiField.normAt f x :=
  le_ciSup (f := fun i => |f (i, x)|) (Set.finite_range _).bddAbove i
end Seminorms
end CenteredCubeDecay
end YangMills.Construction.PeriodicLattice
