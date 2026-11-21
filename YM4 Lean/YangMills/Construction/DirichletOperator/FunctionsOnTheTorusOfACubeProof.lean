import YangMills.Construction.DirichletOperator.FunctionsOnTheTorusOfACube
import YangMills.Construction.DirichletOperator.NormsOfAFormCarriedFromTheTorusOfACubeProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.CubeTorus (TensorAnchorSupported)
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
namespace CubeObservable
section Generic
variable {α β : Type} {P : α → Prop} {e : α → β} {f : α → ℝ} {g : β → ℝ}
end Generic
section Transfer
variable {P α β : Type} [TopologicalSpace P] {e : α → β} {p : α → P} {X : Set P}
end Transfer
theorem proj_neg_eq {S : ℝ} (v : Fin 4 → ℝ) : torusProj 4 S (-v) = -torusProj 4 S v := by apply _root_.YangMills.Construction.PartitionCubes.TorusTransfer.torusProj_neg <;> assumption
theorem proj_add_eq {S : ℝ} (v w : Fin 4 → ℝ) :
    torusProj 4 S (v + w) = torusProj 4 S v + torusProj 4 S w := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_add <;> assumption
theorem supNorm_sub_comm {S : ℝ} (p q : PeriodicTorus 4 S) : supNorm (p - q) = supNorm (q - p) := by apply _root_.YangMills.Construction.PartitionCubes.TorusComponents.supNorm_sub_comm <;> assumption
theorem supNorm_proj_le {S : ℝ} (v : Fin 4 → ℝ) : supNorm (torusProj 4 S v) ≤ ‖v‖ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.supNorm_proj_le <;> assumption
theorem finite_fineSite (hT : TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
theorem finite_fineBond (hT : TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
variable {𝒮 : NestedRegions} {M : ℕ} {Q : LevelCube 𝒮 M}
structure FirstTypeData (Q : LevelCube 𝒮 M) : Prop where
  isometry : Q.EmbeddingProperties
  transfer : Q.TransfersToTorus
  props : Q.FirstTypeProperties
  lengths : TorusLengthsStatement
  proj : ProjectionFacts 4 𝒮.side
  scale_pos : 0 < 𝒮.scale (Q.level + 1)
  eight_mul_le : 8 * 𝒮.scale (Q.level + 1) ≤ 𝒮.side / 2
  ξ_le : 𝒮.ξ ≤ 𝒮.scale (Q.level + 1)
namespace FirstTypeData
variable (H : FirstTypeData Q)
include H
theorem lengthAxioms : LengthAxioms 4 𝒮.side := (H.lengths 4 𝒮.side 𝒮.side_pos).1
theorem mem_strictPts_of_near {x x' : 𝒮.Point} (hx : x ∈ Q.thicken (5 / 6))
    (h : supNorm (x' - x) ≤ 4 * 𝒮.scale (Q.level + 1)) : x' ∈ Q.strictPts :=
  (H.transfer.isometry_ball x hx x' (by rwa [supNorm_sub_comm])).1
theorem thicken_subset_strictPts : Q.thicken (5 / 6) ⊆ Q.strictPts := fun x hx =>
  H.mem_strictPts_of_near hx (by
    rw [sub_self, H.lengthAxioms.supNorm_zero]
    have := H.scale_pos
    positivity)
theorem embed_injOn : InjOn Q.system.embed Q.strictPts := H.props.embed_bijective.injOn
theorem scale_zero_eq : 𝒮.scale 0 = Q.system.setting.ξ := by
  rw [H.transfer.ξ_eq]
  simp [RegionSequence.NestedRegions.scale, scaleSpacing]
theorem mapSite_coe (x : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ Q.strictPts) :
    ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) =
      Q.system.embed x := by
  have hξ : 𝒮.scale 0 = 𝒮.ξ := H.scale_zero_eq.trans H.transfer.ξ_eq
  have h2 : Q.system.embed x ∈ Q.system.embed ''
      ((spacingLattice 4 𝒮.side (𝒮.scale 0) : Set 𝒮.Point) ∩ Q.strictPts) :=
    ⟨x, ⟨by rw [hξ]; exact x.2, hx⟩, rfl⟩
  rw [H.props.embed_sites 0 (Or.inl (Nat.zero_le _)), H.scale_zero_eq] at h2
  exact Classical.epsilon_spec
    (p := fun y : Q.system.setting.FineSite => (y : Q.system.setting.Point) = Q.system.embed x)
    ⟨⟨_, h2.1⟩, rfl⟩
theorem exists_lift_near {q : Fin 4 → ℝ} (hq : q ∈ Q.liftedOpenCube)
    (hs : torusProj 4 𝒮.side q ∈ Q.thicken (5 / 6)) {x : 𝒮.Point}
    (hx : supNorm (x - torusProj 4 𝒮.side q) ≤ 4 * 𝒮.scale (Q.level + 1)) :
    ∃ p ∈ Q.liftedOpenCube, torusProj 4 𝒮.side p = x ∧
      ‖q - p‖ = supNorm (x - torusProj 4 𝒮.side q) := by
  have F := H.props
  have hx' : supNorm (torusProj 4 𝒮.side q - x) ≤ 4 * 𝒮.scale (Q.level + 1) := by
    rwa [supNorm_sub_comm]
  obtain ⟨hin, hsup, -⟩ := H.transfer.isometry_ball _ hs x hx'
  obtain ⟨p, hp, rfl⟩ := F.cover_bijective.surjOn hin
  refine ⟨p, hp, rfl, ?_⟩
  rw [F.embed_cover q hq, F.embed_cover p hp, F.local_supLength q hq p hp] at hsup
  rw [hsup, supNorm_sub_comm]
theorem embed_add_proj {s : 𝒮.Point} (hs : s ∈ Q.thicken (5 / 6)) (v : Fin 4 → ℝ)
    (hv : ‖v‖ ≤ 4 * 𝒮.scale (Q.level + 1)) :
    Q.system.embed (s + torusProj 4 𝒮.side v) =
      Q.system.embed s + torusProj 4 Q.system.setting.side v := by
  have F := H.props
  obtain ⟨q, hq, rfl⟩ := F.cover_bijective.surjOn (H.thicken_subset_strictPts hs)
  have hx : supNorm (torusProj 4 𝒮.side q + torusProj 4 𝒮.side v - torusProj 4 𝒮.side q) ≤
      4 * 𝒮.scale (Q.level + 1) := by
    rw [add_sub_cancel_left]
    exact (supNorm_proj_le v).trans hv
  obtain ⟨p, hp, hpc, hpq⟩ := H.exists_lift_near hq hs hx
  have hshort : ‖p - (q + v)‖ ≤ 𝒮.side / 2 := by
    have h₁ : ‖p - (q + v)‖ ≤ ‖q - p‖ + ‖v‖ := by
      have : p - (q + v) = -(q - p) + -v := by abel
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, norm_neg]
    linarith [H.eight_mul_le]
  have hz := H.proj.supNorm_eq p (q + v) hshort
  rw [hpc, proj_add_eq, sub_self, H.lengthAxioms.supNorm_zero] at hz
  have hpe : p = q + v := sub_eq_zero.1 (norm_eq_zero.1 hz.symm)
  exact F.embed_add q v hq (hpe ▸ hp)
theorem exists_vec_near {s x : 𝒮.Point} (hs : s ∈ Q.thicken (5 / 6)) {r : ℝ}
    (hx : supNorm (x - s) ≤ r) (hr : r ≤ 4 * 𝒮.scale (Q.level + 1)) :
    ∃ v : Fin 4 → ℝ, ‖v‖ ≤ r ∧ x = s + torusProj 4 𝒮.side v := by
  have F := H.props
  obtain ⟨q, hq, rfl⟩ := F.cover_bijective.surjOn (H.thicken_subset_strictPts hs)
  obtain ⟨p, hp, rfl, hpq⟩ := H.exists_lift_near hq hs (hx.trans hr)
  refine ⟨p - q, ?_, ?_⟩
  · rw [norm_sub_rev, hpq]
    exact hx
  · rw [← proj_add_eq, add_sub_cancel]
theorem shift_near {s x : 𝒮.Point} (hs : s ∈ Q.thicken (5 / 6))
    (hx : supNorm (x - s) ≤ 3 * 𝒮.scale (Q.level + 1)) {w : Fin 4 → ℝ}
    (hw : ‖w‖ ≤ 𝒮.scale (Q.level + 1)) :
    x ∈ Q.strictPts ∧ x + torusProj 4 𝒮.side w ∈ Q.strictPts ∧
      Q.system.embed (x + torusProj 4 𝒮.side w) =
        Q.system.embed x + torusProj 4 Q.system.setting.side w := by
  have hp := H.scale_pos
  obtain ⟨v, hv, rfl⟩ := H.exists_vec_near hs hx (by linarith)
  have hvw : ‖v + w‖ ≤ 4 * 𝒮.scale (Q.level + 1) := by
    have := norm_add_le v w
    linarith
  refine ⟨H.mem_strictPts_of_near hs (by linarith), H.mem_strictPts_of_near hs ?_, ?_⟩
  · have : s + torusProj 4 𝒮.side v + torusProj 4 𝒮.side w - s = torusProj 4 𝒮.side (v + w) := by
      rw [proj_add_eq]
      abel
    rw [this]
    exact (supNorm_proj_le _).trans hvw
  · rw [add_assoc, ← proj_add_eq, H.embed_add_proj hs (v + w) hvw,
      H.embed_add_proj hs v (by linarith), proj_add_eq, add_assoc]
theorem norm_single_le_scale (ν : Fin 4) : ‖(Pi.single ν 𝒮.ξ : Fin 4 → ℝ)‖ ≤
    𝒮.scale (Q.level + 1) := by
  have hξ := 𝒮.ξ_pos
  refine (pi_norm_le_iff_of_nonneg H.scale_pos.le).2 fun μ => ?_
  by_cases h : μ = ν
  · subst h
    simp only [Pi.single_eq_same, Real.norm_eq_abs, abs_of_pos hξ]
    exact H.ξ_le
  · simp only [Pi.single_eq_of_ne h, norm_zero]
    exact H.scale_pos.le
theorem mapSite_add_unitStep {s : 𝒮.Point} (hs : s ∈ Q.thicken (5 / 6)) (ν : Fin 4)
    (x : 𝒮.FineSite) (hx : supNorm ((x : 𝒮.Point) - s) ≤ 3 * 𝒮.scale (Q.level + 1)) :
    Q.system.mapSite (x + unitStep 4 𝒮.side 𝒮.ξ ν) =
      Q.system.mapSite x + unitStep 4 Q.system.setting.side Q.system.setting.ξ ν := by
  obtain ⟨h₁, h₂, h₃⟩ := H.shift_near hs hx (H.norm_single_le_scale ν)
  have c₁ : ((x + unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) =
      (x : 𝒮.Point) + torusProj 4 𝒮.side (Pi.single ν 𝒮.ξ) := rfl
  apply Subtype.ext
  rw [H.mapSite_coe _ (by rw [c₁]; exact h₂), c₁, h₃]
  change _ = ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) +
    torusProj 4 Q.system.setting.side (Pi.single ν Q.system.setting.ξ)
  rw [H.mapSite_coe x h₁, H.transfer.ξ_eq]
theorem mapSite_sub_unitStep {s : 𝒮.Point} (hs : s ∈ Q.thicken (5 / 6)) (ν : Fin 4)
    (x : 𝒮.FineSite) (hx : supNorm ((x : 𝒮.Point) - s) ≤ 3 * 𝒮.scale (Q.level + 1)) :
    Q.system.mapSite (x - unitStep 4 𝒮.side 𝒮.ξ ν) =
      Q.system.mapSite x - unitStep 4 Q.system.setting.side Q.system.setting.ξ ν := by
  obtain ⟨h₁, h₂, h₃⟩ := H.shift_near hs hx (w := -Pi.single ν 𝒮.ξ)
    (by rw [norm_neg]; exact H.norm_single_le_scale ν)
  have c₁ : ((x - unitStep 4 𝒮.side 𝒮.ξ ν : 𝒮.FineSite) : 𝒮.Point) =
      (x : 𝒮.Point) + torusProj 4 𝒮.side (-Pi.single ν 𝒮.ξ) := by
    rw [proj_neg_eq, ← sub_eq_add_neg]
    rfl
  apply Subtype.ext
  rw [H.mapSite_coe _ (by rw [c₁]; exact h₂), c₁, h₃]
  change _ = ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) -
    torusProj 4 Q.system.setting.side (Pi.single ν Q.system.setting.ξ)
  rw [H.mapSite_coe x h₁, H.transfer.ξ_eq, proj_neg_eq, ← sub_eq_add_neg]
end FirstTypeData
end CubeObservable
end YangMills.Construction
