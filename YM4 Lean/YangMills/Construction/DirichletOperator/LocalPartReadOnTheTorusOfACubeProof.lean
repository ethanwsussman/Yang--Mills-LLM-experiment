import YangMills.Construction.DirichletOperator.CommutatorOfTheLongitudinalOperatorOfACubeProof
import YangMills.Construction.DirichletOperator.BoundsOfTheBracketOnALocalTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
namespace TorusBracketLocalPart
variable {𝒩 : RegionSequence.NestedRegions} {M : ℕ}
theorem supNorm_torusProj_le {S : ℝ} (w : Fin 4 → ℝ) : supNorm (torusProj 4 S w) ≤ ‖w‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_proj_le <;> assumption
theorem torusProj_neg {S : ℝ} (u : Fin 4 → ℝ) : torusProj 4 S (-u) = -torusProj 4 S u := by apply _root_.YangMills.Construction.PartitionCubes.TorusTransfer.torusProj_neg <;> assumption
theorem torusProj_zero {S : ℝ} : torusProj 4 S 0 = 0 := by apply _root_.YangMills.Construction.CubeCommutator.torusProj_zero <;> assumption
theorem norm_piSingle_le {ξ : ℝ} (hξ : 0 ≤ ξ) (ν : Fin 4) : ‖(Pi.single ν ξ : Fin 4 → ℝ)‖ ≤ ξ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.norm_pi_single_le <;> assumption
theorem mem_thicken_of_near (Q : LevelCube 𝒩 M) (hr : 12 * 𝒩.ξ ≤ mollifyRadius 𝒩 M Q.level)
    {x p : 𝒩.Point} (hp : p ∈ Q.supp) (h : supNorm (x - p) ≤ 𝒩.ξ) : x ∈ Q.thicken (5 / 6) := by
  change supSetDist {x} Q.supp ≤ _
  have h₁ : supSetDist {x} Q.supp ≤ ENNReal.ofReal (supNorm (x - p)) :=
    iInf₂_le_of_le _ rfl (iInf₂_le _ hp)
  refine h₁.trans (ENNReal.ofReal_le_ofReal ?_)
  have := 𝒩.ξ_pos
  linarith
end TorusBracketLocalPart
end YangMills.Construction
