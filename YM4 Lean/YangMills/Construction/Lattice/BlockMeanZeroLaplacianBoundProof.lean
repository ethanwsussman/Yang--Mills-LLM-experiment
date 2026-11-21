import YangMills.Construction.Lattice.DifferenceOperatorsCellAveragesTrees
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
namespace CellMeanZero
variable {d L j N : ℕ} (S : Scales d L j N)
def cellSite (c : GridPoint d S.coarseMesh) (σ : Fin d → Fin L) : GridPoint d S.unitMesh :=
  S.coarseToUnit c + ∑ μ, (σ μ : ℕ) • S.unitMesh.basisStep μ
theorem cellSite_apply (c : GridPoint d S.coarseMesh) (σ : Fin d → Fin L) (ν : Fin d) :
    ((cellSite S c σ : GridPoint d S.unitMesh) : Torus d N) ν =
      (c : Torus d N) ν + (((σ ν : ℕ) : ℝ) : AddCircle (N : ℝ)) := by
  have hsum : ((∑ μ, (σ μ : ℕ) • S.unitMesh.basisStep μ : GridPoint d S.unitMesh) : Torus d N) =
      ∑ μ, (σ μ : ℕ) • axisMultiple μ (1 : ℝ) := by
    rw [AddSubgroup.val_finsetSum]
    rfl
  have hcoord : (∑ μ, (σ μ : ℕ) • axisMultiple (N := N) μ (1 : ℝ)) ν =
      (((σ ν : ℕ) : ℝ) : AddCircle (N : ℝ)) := by
    rw [Finset.sum_apply, Finset.sum_eq_single ν]
    · simp only [axisMultiple, Pi.smul_apply, Pi.single_eq_same]
      rw [← AddCircle.coe_nsmul, nsmul_eq_mul, mul_one]
    · intro μ _ hμν
      simp [axisMultiple, Pi.single_eq_of_ne hμν.symm]
    · simp
  change ((S.coarseToUnit c : GridPoint d S.unitMesh) : Torus d N) ν +
    ((∑ μ, (σ μ : ℕ) • S.unitMesh.basisStep μ : GridPoint d S.unitMesh) : Torus d N) ν = _
  rw [hsum, hcoord]
  rfl
theorem mem_coarseCell_iff (c : GridPoint d S.coarseMesh) (x : GridPoint d S.unitMesh) :
    x ∈ S.coarseCell c ↔ (x : Torus d N) ∈ halfOpenCube (c : Torus d N) (L : ℝ) := by
  simp [Scales.coarseCell, sitesInCube]
theorem cellSite_mem (c : GridPoint d S.coarseMesh) (σ : Fin d → Fin L) :
    cellSite S c σ ∈ S.coarseCell c := by
  refine (mem_coarseCell_iff S c _).mpr ⟨fun μ => ((σ μ : ℕ) : ℝ), fun μ => ⟨?_, ?_⟩,
    funext fun ν => ?_⟩
  · positivity
  · have hσ := (σ μ).2
    change ((σ μ : ℕ) : ℝ) < L
    exact_mod_cast hσ
  · rw [cellSite_apply]
    rfl
end CellMeanZero
open CellMeanZero
end YangMills.Construction.PeriodicLattice
