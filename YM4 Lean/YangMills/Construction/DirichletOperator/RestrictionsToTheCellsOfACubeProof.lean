import YangMills.Construction.DirichletOperator.BondsCarriedToTheTorusOfACube
import YangMills.Construction.DirichletOperator.CellsOfACube
import YangMills.Construction.RegionSequence.CellsAndAdjoints
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.CellRestriction
theorem supNorm_zero_le {S : ℝ} {r : ℝ} (hr : 0 ≤ r) : supNorm (0 : PeriodicTorus 4 S) ≤ r := by
  have hmem : (0 : ℝ) ∈ {r | ∃ v : Fin 4 → ℝ, torusProj 4 S v = (0 : PeriodicTorus 4 S) ∧ r = ‖v‖} :=
    ⟨0, by funext μ; simp [torusProj], by simp⟩
  have hbdd : BddBelow {r | ∃ v : Fin 4 → ℝ, torusProj 4 S v = (0 : PeriodicTorus 4 S) ∧ r = ‖v‖} := by
    refine ⟨0, ?_⟩
    rintro r ⟨v, _, rfl⟩
    exact norm_nonneg v
  exact (csInf_le hbdd hmem).trans hr
variable {R : NestedRegions} {M : ℕ}
end YangMills.Construction.PartitionCubes.CellRestriction
