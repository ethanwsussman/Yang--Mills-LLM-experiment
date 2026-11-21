import YangMills.Construction.DirichletOperator.AdjointDefectOfACubeAsItsSourcesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes RemainderEstimates
namespace RemainderAdjointTerms
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : RegionSequence.NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem bondInner_comm {𝒯 : RegionSequence.NestedRegions} (A B : 𝒯.FineBond → ℝ) :
    bondInner A B = bondInner B A := by apply _root_.YangMills.Construction.RegionSequence.GradientAdjointsOnTorus.bondInner_comm <;> assumption
theorem bondInner_sub_left [Finite 𝒮.FineBond] (A B g : 𝒮.FineBond → ℝ) :
    bondInner (A - B) g = bondInner A g - bondInner B g := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.bondInner_sub_left <;> assumption
theorem eq_zero_of_bondInner_self [Finite 𝒮.FineBond] (D : 𝒮.FineBond → ℝ)
    (h : bondInner D D = 0) : D = 0 := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.eq_zero_of_bondInner_self <;> assumption
theorem supNorm_source_sub_target (b : 𝒮.FineBond) :
    supNorm ((b.source : 𝒮.Point) - (b.target : 𝒮.Point)) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.supNorm_source_sub_target <;> assumption
theorem supNorm_target_sub_source (b : 𝒮.FineBond) :
    supNorm ((b.target : 𝒮.Point) - (b.source : 𝒮.Point)) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.RegionSequence.AnchorCutIdentities.supNorm_target_sub_source <;> assumption
theorem thirteen_mul_ξ_le_cubeSide (hM : 𝒮.L ^ 5 ≤ M) (n : ℕ) :
    13 * 𝒮.ξ ≤ PartitionCubes.cubeSide 𝒮 M n := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.thirteen_mul_ξ_le_cubeSide <;> assumption
theorem tsupport_partitionFn_subset_thicken (hl : Torus.TorusLengthsStatement) (Q : LevelCube 𝒮 M)
    (ς : ℝ) : tsupport Q.partitionFn ⊆ Q.thicken ς := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.tsupport_subset_thicken <;> assumption
theorem pullBonds_mapBond (𝔏 : CubeSystem 𝒮) (φ : 𝒮.Point → ℝ) (A : 𝒮.FineBond → ℝ)
    (b : 𝒮.FineBond)
    (hu : ∀ b' : 𝒮.FineBond, (b'.source : 𝒮.Point) ∈ tsupport φ →
      𝔏.mapBond b' = 𝔏.mapBond b → b' = b) :
    𝔏.pullBonds φ A (𝔏.mapBond b) = φ (b.source : 𝒮.Point) * A b := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.pullBonds_mapBond <;> assumption
structure TransferProperties (Q : LevelCube 𝒮 M) (𝔏 : CubeSystem 𝒮) : Prop where
  pull_mem : ∀ A ∈ 𝒮.oneForms, 𝔏.pullBonds Q.partitionFn A ∈ 𝔏.forms
  push_mem : ∀ v ∈ 𝔏.forms, 𝔏.pushBonds Q.partitionFn v ∈ 𝒮.oneForms
theorem bondInner_add_left [Finite 𝒮.FineBond] (A B g : 𝒮.FineBond → ℝ) :
    bondInner (A + B) g = bondInner A g + bondInner B g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.bondInner_add_left <;> assumption
theorem eq_of_bondInner_eq [Finite 𝒮.FineBond] {X Y : 𝒮.FineBond → ℝ} (hX : X ∈ 𝒮.oneForms)
    (hY : Y ∈ 𝒮.oneForms) (h : ∀ v ∈ 𝒮.oneForms, bondInner X v = bondInner Y v) : X = Y := by
  have hD : bondInner (X - Y) (X - Y) = 0 := by
    rw [bondInner_sub_left, h _ (𝒮.oneForms.sub_mem hX hY), sub_self]
  exact sub_eq_zero.mp (eq_zero_of_bondInner_self _ hD)
end RemainderAdjointTerms
end YangMills.Construction
