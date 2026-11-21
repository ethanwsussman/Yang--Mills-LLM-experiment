import YangMills.Construction.DirichletOperator.BoundsOfACubeTermOnADivergenceProof
import YangMills.Construction.DirichletOperator.FloorsOfThePropagator
import YangMills.Construction.DirichletOperator.LawsOfTheApproximateInverse
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes PropagatorThresholds
  RemainderEstimates
namespace CubeInverseTerms
variable {𝒮 : NestedRegions} {M : ℕ}
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem mapBond_secondType (Q : LevelCube 𝒮 M) (e : 𝒮.FineBond) :
    Q.secondTypeSystem.mapBond e = e := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.mapBond_secondType <;> assumption
theorem tsupport_subset_thicken (hl : Torus.TorusLengthsStatement) (Q : LevelCube 𝒮 M) (ς : ℝ) :
    tsupport Q.partitionFn ⊆ Q.thicken ς := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.tsupport_subset_thicken <;> assumption
theorem supNorm_target_sub_source_le (e : 𝒮.FineBond) :
    supNorm ((e.target : 𝒮.Point) - (e.source : 𝒮.Point)) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.RegionSequence.AnchorCutIdentities.supNorm_target_sub_source <;> assumption
theorem thirteen_mul_ξ_le_cubeSide (hM : 𝒮.L ^ 5 ≤ M) (n : ℕ) : 13 * 𝒮.ξ ≤ cubeSide 𝒮 M n := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.thirteen_mul_ξ_le_cubeSide <;> assumption
theorem inv_mem_forms (𝔏 : CubeSystem 𝒮)
    (hb : BijOn 𝔏.op (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.forms)
    {u : 𝔏.setting.FineBond → ℝ} (hu : u ∈ 𝔏.forms) : 𝔏.inv u ∈ 𝔏.forms := by apply _root_.YangMills.Construction.CubeTermBounds.inv_mem_forms <;> assumption
end CubeInverseTerms
end YangMills.Construction
