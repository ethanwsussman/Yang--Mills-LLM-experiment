import YangMills.Construction.DirichletOperator.CornerBoundsOnTheToriOfTheCubesProof
import YangMills.Construction.DirichletOperator.BoundsOfACubeTermOnADivergenceProof
import YangMills.Construction.DirichletOperator.CubeNearASiteProof
import YangMills.Construction.DirichletOperator.DecayOfAFormFromBoundsOnSmallCubes
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.DirichletOperator.SmallCubeDecay (PointwiseBounds L2Bounds weightFrom)
open YangMills.Construction.CubeOperators (chosenConstants IsCubeScale)
open YangMills.Construction.CubeTorus (levelSpacing tensorModulusAt)
noncomputable section
namespace YangMills.Construction.CubeGreenCell
theorem finite_fineBond (hl : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem supBond_nonneg {𝒯 : NestedRegions} (f : 𝒯.FineBond → ℝ) : 0 ≤ supBond f := by apply _root_.YangMills.Construction.CornerGreen.supBond_nonneg' <;> assumption
theorem ltwoBond_nonneg {𝒯 : NestedRegions} (f : 𝒯.FineBond → ℝ) : 0 ≤ ltwoBond f := by apply _root_.YangMills.Construction.CornerGreen.ltwoBond_nonneg' <;> assumption
theorem supSite_nonneg {𝒯 : NestedRegions} (f : 𝒯.FineSite → ℝ) : 0 ≤ supSite f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem nestedScale_pos (𝒯 : NestedRegions) (n : ℕ) : 0 < 𝒯.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
variable {𝒮 : NestedRegions} {M : ℕ}
theorem pullBonds_mapBond (𝔏 : CubeSystem 𝒮) (φ : 𝒮.Point → ℝ) (A : 𝒮.FineBond → ℝ)
    (b : 𝒮.FineBond)
    (hu : ∀ b' : 𝒮.FineBond, (b'.source : 𝒮.Point) ∈ tsupport φ →
      𝔏.mapBond b' = 𝔏.mapBond b → b' = b) :
    𝔏.pullBonds φ A (𝔏.mapBond b) = φ (b.source : 𝒮.Point) * A b := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.pullBonds_mapBond <;> assumption
theorem tsupport_subset_thicken (hl : TorusLengthsStatement) (Q : LevelCube 𝒮 M) (ς : ℝ) :
    tsupport Q.partitionFn ⊆ Q.thicken ς := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.tsupport_subset_thicken <;> assumption
theorem supNorm_target_sub_source (b : 𝒮.FineBond) :
    supNorm ((b.target : 𝒮.Point) - (b.source : 𝒮.Point)) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.RegionSequence.AnchorCutIdentities.supNorm_target_sub_source <;> assumption
theorem thirteen_mul_ξ_le_cubeSide (hM : 𝒮.L ^ 5 ≤ M) (n : ℕ) : 13 * 𝒮.ξ ≤ cubeSide 𝒮 M n := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.thirteen_mul_ξ_le_cubeSide <;> assumption
theorem inv_mem_forms (𝔏 : CubeSystem 𝒮)
    (hb : BijOn 𝔏.op (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.forms)
    {u : 𝔏.setting.FineBond → ℝ} (hu : u ∈ 𝔏.forms) : 𝔏.inv u ∈ 𝔏.forms := by apply _root_.YangMills.Construction.CubeTermBounds.inv_mem_forms <;> assumption
theorem mem_centresAt_level {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres) :
    y ∈ 𝒮.centresAt (𝒮.level y) := by apply _root_.YangMills.Construction.CubeNearSite.mem_centresAt_level <;> assumption
end YangMills.Construction.CubeGreenCell
