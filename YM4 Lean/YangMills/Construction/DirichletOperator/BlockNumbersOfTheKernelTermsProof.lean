import YangMills.Construction.DirichletOperator.AdjointOfTheRemainderAsASumProof
import YangMills.Construction.DirichletOperator.AdjointTermsAsOperatorsOnFormsProof
import YangMills.Construction.DirichletOperator.BlockNumbersOfTheAdjointTermsProof
import YangMills.Construction.DirichletOperator.CubeNearASiteProof
import YangMills.Construction.DirichletOperator.DefectAsTheSumOfItsKernels
import YangMills.Construction.DirichletOperator.FormDecayingFromAPointOfACube
import YangMills.Construction.DirichletOperator.PositionOfTheCubesByKindProof
import YangMills.Construction.DirichletOperator.PropagatorBoundsForSourcesInFormsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.RemainderEstimates
namespace KernelTermBlocks
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : RegionSequence.NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem cornerSet_finite (hl : Torus.TorusLengthsStatement) (n : ℕ)
    (hσ : 0 < cubeSide 𝒮 M n) (hk : ∃ k : ℤ, 𝒮.side / cubeSide 𝒮 M n = 2 * (k : ℝ)) :
    (cornerSet 𝒮 M n).Finite := by apply _root_.YangMills.Construction.RemainderAdjointSum.cornerSet_finite <;> assumption
theorem finite_levelCube (hc : ∀ n ≤ topLevel 𝒮, (cornerSet 𝒮 M n).Finite) :
    Finite (LevelCube 𝒮 M) := by apply _root_.YangMills.Construction.RemainderAdjointSum.finite_levelCube <;> assumption
theorem bondInner_comm {𝒯 : RegionSequence.NestedRegions} (A B : 𝒯.FineBond → ℝ) :
    bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem bondInner_sub_left [Finite 𝒮.FineBond] (A B g : 𝒮.FineBond → ℝ) :
    bondInner (A - B) g = bondInner A g - bondInner B g := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.bondInner_sub_left <;> assumption
theorem eq_zero_of_bondInner_self [Finite 𝒮.FineBond] (D : 𝒮.FineBond → ℝ)
    (h : bondInner D D = 0) : D = 0 := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.eq_zero_of_bondInner_self <;> assumption
theorem supNorm_source_sub_target (e : 𝒮.FineBond) :
    supNorm ((e.source : 𝒮.Point) - (e.target : 𝒮.Point)) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.supNorm_source_sub_target <;> assumption
theorem supNorm_target_sub_source (e : 𝒮.FineBond) :
    supNorm ((e.target : 𝒮.Point) - (e.source : 𝒮.Point)) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.RegionSequence.AnchorCutIdentities.supNorm_target_sub_source <;> assumption
theorem thirteen_le_cast (hM : 𝒮.L ^ 5 ≤ M) : (13 : ℝ) ≤ M := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.thirteen_le_cast <;> assumption
theorem ξ_le_scale (n : ℕ) : 𝒮.ξ ≤ 𝒮.scale n := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.ξ_le_scale <;> assumption
theorem mem_Ω_zero_of_near (hl : Torus.TorusLengthsStatement) {X : Set 𝒮.Point} (hM : (1 : ℝ) ≤ M)
    (hway : ENNReal.ofReal ((M : ℝ) * 𝒮.ξ) < supSetDist X (𝒮.cubeComplementAt 0 (𝒮.Ω 0)))
    (x y : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ X)
    (hd : supNorm ((x : 𝒮.Point) - (y : 𝒮.Point)) ≤ 𝒮.ξ) : (y : 𝒮.Point) ∈ 𝒮.Ω 0 := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.mem_Ω_zero_of_near <;> assumption
theorem tsupport_partitionFn_subset_thicken (hl : Torus.TorusLengthsStatement) (Q : LevelCube 𝒮 M)
    (ς : ℝ) : tsupport Q.partitionFn ⊆ Q.thicken ς := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.tsupport_subset_thicken <;> assumption
theorem cubeSide_pos (hM : 𝒮.L ^ 5 ≤ M) (n : ℕ) : 0 < cubeSide 𝒮 M n := by apply _root_.YangMills.Construction.PartitionCubes.PositionByType.cubeSide_pos <;> assumption
theorem mem_centresAt_level {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres) :
    y ∈ 𝒮.centresAt (𝒮.level y) := by apply _root_.YangMills.Construction.CubeNearSite.mem_centresAt_level <;> assumption
theorem pullBonds_mapBond (𝔏 : CubeSystem 𝒮) (φ : 𝒮.Point → ℝ) (A : 𝒮.FineBond → ℝ)
    (e : 𝒮.FineBond)
    (hu : ∀ e' : 𝒮.FineBond, (e'.source : 𝒮.Point) ∈ tsupport φ →
      𝔏.mapBond e' = 𝔏.mapBond e → e' = e) :
    𝔏.pullBonds φ A (𝔏.mapBond e) = φ (e.source : 𝒮.Point) * A e := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.pullBonds_mapBond <;> assumption
structure TransferProperties (Q : LevelCube 𝒮 M) (𝔏 : CubeSystem 𝒮) : Prop where
  pull_mem : ∀ A ∈ 𝒮.oneForms, 𝔏.pullBonds Q.partitionFn A ∈ 𝔏.forms
  push_mem : ∀ v ∈ 𝔏.forms, 𝔏.pushBonds Q.partitionFn v ∈ 𝒮.oneForms
theorem inv_spec (𝔏 : CubeSystem 𝒮)
    (hb : BijOn 𝔏.op (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.forms)
    {u : 𝔏.setting.FineBond → ℝ} (hu : u ∈ 𝔏.forms) :
    𝔏.inv u ∈ 𝔏.forms ∧ 𝔏.op (𝔏.inv u) = u := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.cubeInv_spec <;> assumption
theorem inv_zero (𝔏 : CubeSystem 𝒮) [Finite 𝔏.setting.FineBond]
    (hb : BijOn 𝔏.op (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.forms)
    (hs : ∀ u ∈ 𝔏.forms, ∀ v ∈ 𝔏.forms, bondInner (𝔏.inv u) v = bondInner u (𝔏.inv v)) :
    𝔏.inv 0 = 0 := by
  have h₀ := (inv_spec 𝔏 hb 𝔏.forms.zero_mem).1
  refine eq_zero_of_bondInner_self _ ?_
  rw [hs 0 𝔏.forms.zero_mem _ h₀]
  simp [bondInner]
end KernelTermBlocks
end YangMills.Construction
