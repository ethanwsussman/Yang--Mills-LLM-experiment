import YangMills.Construction.DirichletOperator.GreenOperatorOfACubeOnAFormOfACellProof
import YangMills.Construction.DirichletOperator.HolderBoundOfTheAdjointOfTheRemainderProof
import YangMills.Construction.DirichletOperator.SourcesOfATermOfACubeAtTheCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
namespace CellSources
theorem finite_fineBond (hl : Torus.TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem scale_pos (𝒯 : NestedRegions) (n : ℕ) : 0 < 𝒯.scale n := by apply _root_.YangMills.Construction.RegionSequence.AvgOpWeightSum.scale_pos <;> assumption
variable {𝒮 : NestedRegions} {M : ℕ}
theorem pullBonds_mapBond (𝔏 : CubeSystem 𝒮) (φ : 𝒮.Point → ℝ) (A : 𝒮.FineBond → ℝ)
    (b : 𝒮.FineBond)
    (hu : ∀ b' : 𝒮.FineBond, (b'.source : 𝒮.Point) ∈ tsupport φ →
      𝔏.mapBond b' = 𝔏.mapBond b → b' = b) :
    𝔏.pullBonds φ A (𝔏.mapBond b) = φ (b.source : 𝒮.Point) * A b := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.pullBonds_mapBond <;> assumption
theorem tsupport_partitionFn_subset_thicken (hl : Torus.TorusLengthsStatement) (Q : LevelCube 𝒮 M)
    (ς : ℝ) : tsupport Q.partitionFn ⊆ Q.thicken ς := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.tsupport_subset_thicken <;> assumption
theorem supNorm_target_sub_source (b : 𝒮.FineBond) :
    supNorm ((b.target : 𝒮.Point) - (b.source : 𝒮.Point)) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.RegionSequence.AnchorCutIdentities.supNorm_target_sub_source <;> assumption
theorem thirteen_mul_ξ_le_cubeSide (hM : 𝒮.L ^ 5 ≤ M) (n : ℕ) : 13 * 𝒮.ξ ≤ cubeSide 𝒮 M n := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.thirteen_mul_ξ_le_cubeSide <;> assumption
theorem inv_mem_forms (𝔏 : CubeSystem 𝒮)
    (hb : BijOn 𝔏.op (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.forms)
    {u : 𝔏.setting.FineBond → ℝ} (hu : u ∈ 𝔏.forms) : 𝔏.inv u ∈ 𝔏.forms := by apply _root_.YangMills.Construction.CubeTermBounds.inv_mem_forms <;> assumption
theorem mem_centresAt_level {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres) :
    y ∈ 𝒮.centresAt (𝒮.level y) := by apply _root_.YangMills.Construction.CubeNearSite.mem_centresAt_level <;> assumption
theorem bondInner_add {𝒯 : NestedRegions} [Finite 𝒯.FineBond] (A B g : 𝒯.FineBond → ℝ) :
    bondInner (A + B) g = bondInner A g + bondInner B g := by apply _root_.YangMills.Construction.RegionSequence.Positivity.bondInner_add_left <;> assumption
theorem bondInner_sub {𝒯 : NestedRegions} [Finite 𝒯.FineBond] (A B g : 𝒯.FineBond → ℝ) :
    bondInner (A - B) g = bondInner A g - bondInner B g := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.bondInner_sub_left <;> assumption
theorem eq_zero_of_bondInner_self {𝒯 : NestedRegions} [Finite 𝒯.FineBond] (D : 𝒯.FineBond → ℝ)
    (h : bondInner D D = 0) : D = 0 := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.eq_zero_of_bondInner_self <;> assumption
theorem inv_add (𝔏 : CubeSystem 𝒮) [Finite 𝔏.setting.FineBond]
    (hb : BijOn 𝔏.op (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.forms)
    (hs : ∀ u ∈ 𝔏.forms, ∀ v ∈ 𝔏.forms, bondInner (𝔏.inv u) v = bondInner u (𝔏.inv v))
    {u v : 𝔏.setting.FineBond → ℝ} (hu : u ∈ 𝔏.forms) (hv : v ∈ 𝔏.forms) :
    𝔏.inv (u + v) = 𝔏.inv u + 𝔏.inv v := by
  have huv := 𝔏.forms.add_mem hu hv
  set D := 𝔏.inv (u + v) - (𝔏.inv u + 𝔏.inv v) with hD
  have hDm : D ∈ 𝔏.forms := 𝔏.forms.sub_mem (inv_mem_forms 𝔏 hb huv)
    (𝔏.forms.add_mem (inv_mem_forms 𝔏 hb hu) (inv_mem_forms 𝔏 hb hv))
  have h0 : bondInner D D = 0 := by
    conv_lhs => rw [hD]
    rw [bondInner_sub, bondInner_add, hs _ huv _ hDm, hs _ hu _ hDm, hs _ hv _ hDm,
      bondInner_add]
    ring
  exact sub_eq_zero.mp (eq_zero_of_bondInner_self D h0)
theorem inv_sum (𝔏 : CubeSystem 𝒮) [Finite 𝔏.setting.FineBond]
    (hb : BijOn 𝔏.op (𝔏.forms : Set (𝔏.setting.FineBond → ℝ)) 𝔏.forms)
    (hs : ∀ u ∈ 𝔏.forms, ∀ v ∈ 𝔏.forms, bondInner (𝔏.inv u) v = bondInner u (𝔏.inv v))
    (t : Finset 𝒮.Point) (g : 𝒮.Point → 𝔏.setting.FineBond → ℝ) (hg : ∀ y ∈ t, g y ∈ 𝔏.forms) :
    𝔏.inv (∑ y ∈ t, g y) = ∑ y ∈ t, 𝔏.inv (g y) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h := inv_add 𝔏 hb hs 𝔏.forms.zero_mem 𝔏.forms.zero_mem
    rw [add_zero] at h
    simpa using h
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      inv_add 𝔏 hb hs (hg a (Finset.mem_insert_self a t))
        (𝔏.forms.sum_mem fun y hy => hg y (Finset.mem_insert_of_mem hy)),
      ih fun y hy => hg y (Finset.mem_insert_of_mem hy)]
end CellSources
end YangMills.Construction
