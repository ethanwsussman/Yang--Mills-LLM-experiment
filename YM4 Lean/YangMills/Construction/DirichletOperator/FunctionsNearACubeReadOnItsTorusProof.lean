import YangMills.Construction.DirichletOperator.BondsCarriedToTheTorusOfACubeProof
import YangMills.Construction.DirichletOperator.FactsOfALocalOperatorOfACube
import YangMills.Construction.DirichletOperator.IsometryOfACubeOnSmallBalls
import YangMills.Construction.RegionSequence.DifferenceAdjointsByParts
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes.TorusComponents
section Suprema
end Suprema
theorem torusProj_neg {S : ℝ} (v : Fin 4 → ℝ) : torusProj 4 S (-v) = -torusProj 4 S v := by apply _root_.YangMills.Construction.PartitionCubes.TorusTransfer.torusProj_neg <;> assumption
theorem supNorm_neg {S : ℝ} (p : PeriodicTorus 4 S) : supNorm (-p) = supNorm p := by
  unfold supNorm
  congr 1
  ext r
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨-v, by rw [torusProj_neg, hv, neg_neg], by simp⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨-v, by rw [torusProj_neg, hv], by simp⟩
theorem supNorm_sub_comm {S : ℝ} (p q : PeriodicTorus 4 S) : supNorm (p - q) = supNorm (q - p) := by
  rw [← neg_sub, supNorm_neg]
variable {𝒮 : NestedRegions} {M : ℕ} {Q : LevelCube 𝒮 M}
structure CubeHyps (Q : LevelCube 𝒮 M) : Prop where
  isometric : Q.IsometricOnBalls
  transfer : Q.TransfersToTorus
  firstType : Q.FirstTypeProperties
  lengths : TorusLengthsStatement
namespace CubeHyps
variable (H : CubeHyps Q)
include H
theorem lengths_ambient : LengthAxioms 4 𝒮.side := (H.lengths 4 𝒮.side 𝒮.side_pos).1
theorem ballRadius_nonneg : 0 ≤ 4 * 𝒮.scale (Q.level + 1) := by
  have hξ := 𝒮.ξ_pos
  unfold NestedRegions.scale scaleSpacing
  positivity
theorem mem_strictPts_of_near {x x' : 𝒮.Point} (hx : x ∈ Q.thicken (5 / 6))
    (h : supNorm (x' - x) ≤ 4 * 𝒮.scale (Q.level + 1)) : x' ∈ Q.strictPts :=
  (H.transfer.isometry_ball x hx x' (by rwa [supNorm_sub_comm])).1
theorem thicken_subset_strictPts : Q.thicken (5 / 6) ⊆ Q.strictPts := fun x hx =>
  H.mem_strictPts_of_near hx
    (by rw [sub_self, H.lengths_ambient.supNorm_zero]; exact H.ballRadius_nonneg)
theorem embed_injOn : InjOn Q.system.embed Q.strictPts := H.firstType.embed_bijective.injOn
theorem scale_zero : 𝒮.scale 0 = Q.system.setting.ξ := by
  rw [H.transfer.ξ_eq]
  simp [NestedRegions.scale, scaleSpacing]
theorem mapSite_coe (x : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ Q.strictPts) :
    ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) =
      Q.system.embed x := by
  have hξ : 𝒮.scale 0 = 𝒮.ξ := H.scale_zero.trans H.transfer.ξ_eq
  have h2 : Q.system.embed x ∈ Q.system.embed ''
      ((spacingLattice 4 𝒮.side (𝒮.scale 0) : Set 𝒮.Point) ∩ Q.strictPts) :=
    ⟨x, ⟨by rw [hξ]; exact x.2, hx⟩, rfl⟩
  rw [H.firstType.embed_sites 0 (Or.inl (Nat.zero_le _)), H.scale_zero] at h2
  exact Classical.epsilon_spec
    (p := fun y : Q.system.setting.FineSite => (y : Q.system.setting.Point) = Q.system.embed x)
    ⟨⟨_, h2.1⟩, rfl⟩
theorem mem_cubeHalfSide_iff {o x : 𝒮.Point} (ho : o ∈ Q.thicken (5 / 6))
    (hx : x ∈ Q.thicken (5 / 6)) {lam : ℝ} (hlam : lam ≤ 4 * 𝒮.scale (Q.level + 1)) :
    x ∈ cubeHalfSide o lam ↔ Q.system.embed x ∈ cubeHalfSide (Q.system.embed o) lam := by
  have hoo : supNorm (o - o) ≤ 4 * 𝒮.scale (Q.level + 1) := by
    rw [sub_self, H.lengths_ambient.supNorm_zero]
    exact H.ballRadius_nonneg
  simp only [cubeHalfSide, cubeAt, mem_ofPred_eq]
  have half : ∀ t : ℝ, 2 * lam / 2 = lam := fun _ => by ring
  rw [half 0]
  constructor
  · intro h
    rw [H.isometric.supNorm_eq o ho x o (h.trans hlam) hoo]
    exact h
  · intro h
    obtain ⟨x', hx', e⟩ := (H.isometric.ball_bijOn o ho).surjOn
      (show Q.system.embed x ∈ {y | supNorm (y - Q.system.embed o) ≤
        4 * 𝒮.scale (Q.level + 1)} from h.trans hlam)
    have hx'i : x' ∈ Q.strictPts := H.mem_strictPts_of_near ho hx'
    have hxx : x' = x := H.embed_injOn hx'i (H.thicken_subset_strictPts hx) e
    subst hxx
    rw [← H.isometric.supNorm_eq o ho x' o hx' hoo]
    exact h
end CubeHyps
section Transfer
variable {P α β : Type} [TopologicalSpace P] {e : α → β} {p : α → P} {X : Set P}
end Transfer
structure Correspondence (Q : LevelCube 𝒮 M) {α β : Type} (e : α → β) (pa : α → 𝒮.Point)
    (pb : β → Q.system.setting.Point) (R : α → α → Prop) (R' : β → β → Prop) : Prop where
  map_point : ∀ a, pa a ∈ Q.strictPts → pb (e a) = Q.system.embed (pa a)
  inj : ∀ a a', pa a ∈ Q.strictPts → pa a' ∈ Q.strictPts → e a = e a' → a = a'
  surj : ∀ (c : β) (x : 𝒮.Point), x ∈ Q.strictPts → pb c = Q.system.embed x →
    ∃ a, pa a = x ∧ e a = c
  rel_iff : ∀ a a', R a a' ↔ R' (e a) (e a')
structure Transported (Q : LevelCube 𝒮 M) {α β : Type} (e : α → β) (pa : α → 𝒮.Point)
    (f : α → ℝ) (g : β → ℝ) : Prop where
  zero_off : ∀ a, pa a ∉ Q.thicken (5 / 6) → f a = 0
  eq_on : ∀ a, pa a ∈ Q.thicken (5 / 6) → g (e a) = f a
  zero_outside : ∀ c, (∀ a, pa a ∈ Q.thicken (5 / 6) → e a ≠ c) → g c = 0
namespace Correspondence
variable {α β : Type} {e : α → β} {pa : α → 𝒮.Point} {pb : β → Q.system.setting.Point}
  {R : α → α → Prop} {R' : β → β → Prop} {f : α → ℝ} {g : β → ℝ}
theorem apply_eq (D : Correspondence Q e pa pb R R') (H : CubeHyps Q) (C : Transported Q e pa f g)
    (a : α) (ha : pa a ∈ Q.strictPts) : g (e a) = f a := by
  by_cases hX : pa a ∈ Q.thicken (5 / 6)
  · exact C.eq_on a hX
  · rw [C.zero_off a hX]
    refine C.zero_outside _ fun a' ha' h => hX ?_
    rwa [← D.inj a' a (H.thicken_subset_strictPts ha') ha h]
end Correspondence
theorem finite_fineSite (hT : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineSite := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineSite <;> assumption
theorem finite_fineBond (hT : TorusLengthsStatement) (𝒯 : NestedRegions) : Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
end PartitionCubes.TorusComponents
end YangMills.Construction
