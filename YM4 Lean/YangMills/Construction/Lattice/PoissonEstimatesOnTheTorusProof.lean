import YangMills.Construction.FreeKernel.HolderFieldInteriorConstants
import YangMills.Construction.Lattice.GaugeTermOnACubeProof
import YangMills.Construction.Lattice.LiftsOfTheTorusInEveryDimension
import YangMills.Construction.Lattice.PoissonEstimatesOnTheTorus
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice.TorusPoissonProof
open InfiniteLattice (GridSite GridField l1Length supLength gridCube supOver)
variable {d N : ℕ} {ξ : ℝ}
theorem mem_gridCube_iff {X y : GridSite (d + 1) ξ} {r : ℝ} :
    y ∈ gridCube X r ↔ ∀ μ, |(y : Fin (d + 1) → ℝ) μ - (X : Fin (d + 1) → ℝ) μ| ≤ r := by
  change supLength _ ≤ r ↔ _
  unfold supLength
  constructor
  · intro h μ
    exact (le_ciSup (Set.finite_range _).bddAbove μ).trans h
  · exact fun h => ciSup_le h
section Sizes
variable {s : Mesh N}
theorem maxNorm_nonneg (f : SiteFun d s) : 0 ≤ SiteFun.maxNorm f :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem holderSemi_nonneg (σ : ℝ) (F : OneForm d s) : 0 ≤ MultiField.holderSemi σ F := by
  refine Real.sSup_nonneg ?_
  rintro t ⟨x, x', hp, _, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg hp.le _) (Real.iSup_nonneg fun _ => abs_nonneg _)
def cubeSizeConst (d : ℕ) : ℝ := 33 * 9 ^ d + 256
theorem taxicabDist_nonneg (x x' : Torus d N) : 0 ≤ taxicabDist x x' :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _
theorem scaledFun_sum_apply {X ι : Type} (t : Finset ι) (f : ι → ScaledFun d s X) (z : X) :
    (∑ i ∈ t, f i) z = ∑ i ∈ t, f i z := by apply _root_.YangMills.SharedProofs.p17632 <;> assumption
end Sizes
end YangMills.Construction.PeriodicLattice.TorusPoissonProof
