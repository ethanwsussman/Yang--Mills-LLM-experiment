import YangMills.Construction.DirichletOperator.ComparisonEstimatesOnTheCubeProof
import YangMills.Construction.RegionSequence.PartitionConsequences
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open RegionSequence RegionSequence.NestedRegions RegionSequence.CellStructure
namespace PartitionCubes.BracketMatrix
section Lengths
variable {S : ℝ}
theorem exists_lift_abs_eq_norm (p : Torus.PeriodicTorus 4 S) :
    ∃ b : Fin 4 → ℝ, Torus.torusProj 4 S b = p ∧ ∀ μ, |b μ| = ‖p μ‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.exists_lift_abs_eq_norm <;> assumption
theorem norm_apply_le_supNorm (p : Torus.PeriodicTorus 4 S) (ν : Fin 4) :
    ‖p ν‖ ≤ Torus.supNorm p := by apply _root_.YangMills.Construction.RegionSequence.AverageWeightBounds.norm_apply_le_supNorm <;> assumption
theorem supNorm_le_of_forall_norm_le {p : Torus.PeriodicTorus 4 S} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ ν, ‖p ν‖ ≤ r) : Torus.supNorm p ≤ r := by apply _root_.YangMills.Construction.CubeTorusComparison.Estimates.supNorm_le_of_forall_norm_le <;> assumption
end Lengths
section Sums
end Sums
section SeriesExpansions
variable {𝒯 : RegionSequence.NestedRegions}
theorem isPartitionLevel_of_le {j : ℕ} (hj : j ≤ 𝒯.s) : 𝒯.IsPartitionLevel j := by apply _root_.YangMills.Construction.RegionSequence.PartitionConsequences.isPartitionLevel_of_le_s <;> assumption
theorem mem_cubeAt_self {σ : ℝ} (hσ : 0 < σ) (y : 𝒯.Point) : y ∈ Torus.cubeAt y σ := by
  show Torus.supNorm (y - y) ≤ σ / 2
  rw [sub_self]
  exact supNorm_le_of_forall_norm_le (by positivity) fun ν => by
    simpa using (by positivity : 0 ≤ σ / 2)
end SeriesExpansions
section Matrix
variable {𝒯 : RegionSequence.NestedRegions}
def rowCoeff {j : ℕ} (c : 𝒯.BondAt j) (b : 𝒯.FineBond) : ℝ :=
  gaugeParam * 𝒯.scale j ^ (4 - 2) * avgWeight j c b
end Matrix
end PartitionCubes.BracketMatrix
end YangMills.Construction
