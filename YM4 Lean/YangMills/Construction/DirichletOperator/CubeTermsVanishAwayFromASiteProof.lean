import YangMills.Construction.DirichletOperator.CubeTermsVanishAwayFromASite
import YangMills.Construction.DirichletOperator.DivergenceRuleOnTheCubesProof
import YangMills.Construction.DirichletOperator.PropagatorBoundsForDivergenceSourcesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ApproxInverseTerms
open RegionSequence RegionSequence.NestedRegions PartitionCubes ApproxInverseScales
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
theorem supNorm_eq_norm {S : ℝ} (p : Torus.PeriodicTorus 4 S) : Torus.supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem norm_unitStep_le (ν : Fin 4) : ‖(Dirichlet.unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.Point)‖ ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.CubeDivergence.norm_unitStep_le <;> assumption
theorem mem_cubeHalfSide_iff (o x : 𝒮.Point) (t : ℝ) :
    x ∈ cubeHalfSide o t ↔ ‖x - o‖ ≤ t := by
  change Torus.supNorm (x - o) ≤ 2 * t / 2 ↔ _
  rw [supNorm_eq_norm, show 2 * t / 2 = t by ring]
theorem restrictBonds_eq_zero {X : Set 𝒮.Point} {f : 𝒮.FineBond → ℝ}
    (h : ∀ e, AnchoredIn X e → f e = 0) : restrictBonds X f = 0 := by
  funext e
  by_cases he : AnchoredIn X e
  · simp [restrictBonds, indicator, he, h e he]
  · simp [restrictBonds, indicator, he]
end YangMills.Construction.ApproxInverseTerms
