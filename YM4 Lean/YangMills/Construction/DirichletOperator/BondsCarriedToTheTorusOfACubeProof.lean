import YangMills.Construction.Lattice.LatticeIsometriesAsMapsOfPairsProof
import YangMills.Construction.DirichletOperator.AveragingOperatorsAgreeOnTheLocalTorusProof
import YangMills.Construction.DirichletOperator.BondsCarriedToTheTorusOfACube
import YangMills.Construction.DirichletOperator.FunctionsAndMapsOfTheCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
namespace PartitionCubes.TorusTransfer
section Lengths
variable {S : ℝ}
theorem exists_proj_eq_abs_eq_norm (p : PeriodicTorus 4 S) :
    ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ ∀ μ, |v μ| = ‖p μ‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.exists_lift_abs_eq_norm <;> assumption
theorem supNorm_eq_norm (p : PeriodicTorus 4 S) : supNorm p = ‖p‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.supNorm_eq_norm <;> assumption
theorem lOneNorm_eq_sum_norm (p : PeriodicTorus 4 S) : lOneNorm p = ∑ μ, ‖p μ‖ := by
  have hbdd : BddBelow {r | ∃ v : Fin 4 → ℝ, torusProj 4 S v = p ∧ r = ∑ μ, |v μ|} :=
    ⟨0, by rintro _ ⟨v, -, rfl⟩; exact Finset.sum_nonneg fun μ _ => abs_nonneg _⟩
  obtain ⟨b, hb, hb'⟩ := exists_proj_eq_abs_eq_norm p
  apply le_antisymm
  · refine (csInf_le hbdd ⟨b, hb, rfl⟩).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun μ _ => hb' μ
  · refine le_csInf ⟨_, b, hb, rfl⟩ ?_
    rintro _ ⟨v, rfl, rfl⟩
    exact Finset.sum_le_sum fun μ _ => TorusMetric.addCircle_norm_coe_le_abs (v μ)
theorem norm_torusProj_le (w : Fin 4 → ℝ) : ‖torusProj 4 S w‖ ≤ ‖w‖ := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.norm_torusProj_le <;> assumption
theorem torusProj_add (v w : Fin 4 → ℝ) :
    torusProj 4 S (v + w) = torusProj 4 S v + torusProj 4 S w := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.torusProj_add <;> assumption
theorem torusProj_neg (w : Fin 4 → ℝ) : torusProj 4 S (-w) = -torusProj 4 S w := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_neg' <;> assumption
theorem norm_pi_single_of_nonneg {a : ℝ} (ha : 0 ≤ a) (ν : Fin 4) :
    ‖(Pi.single ν a : Fin 4 → ℝ)‖ = a := by
  rw [Pi.norm_single, Real.norm_of_nonneg ha]
end Lengths
variable {𝒮 : NestedRegions} {M : ℕ}
theorem exists_lift_near_centre (Q : LevelCube 𝒮 M) {x : 𝒮.Point} {r : ℝ}
    (h : ‖x - Q.centre‖ < r) :
    ∃ p : Fin 4 → ℝ, torusProj 4 𝒮.side p = x ∧ ∀ μ, |p μ - Q.liftedCentre μ| < r := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.exists_lift_near_centre <;> assumption
structure WellPlaced (Q : LevelCube 𝒮 M) : Prop where
  props : Q.FirstTypeProperties
  ξ_eq : Q.system.setting.ξ = 𝒮.ξ
  step_le : 2 * 𝒮.ξ ≤ 1 / 6 * cubeSide 𝒮 M Q.level
  ball_le : 4 * 𝒮.scale (Q.level + 1) ≤ 1 / 6 * cubeSide 𝒮 M Q.level
  local_ball_le : 2 * Q.system.setting.scale (Q.level + 1) ≤ 1 / 6 * cubeSide 𝒮 M Q.level
  thicken_near : ∀ x ∈ Q.thicken (5 / 6), ‖x - Q.centre‖ < 5 / 6 * cubeSide 𝒮 M Q.level
  supp_near : ∀ x ∈ Q.supp, ‖x - Q.centre‖ < 5 / 6 * cubeSide 𝒮 M Q.level
  side_pos : 0 < cubeSide 𝒮 M Q.level
variable {Q : LevelCube 𝒮 M}
theorem translate_short (H : WellPlaced Q) {x : 𝒮.Point} {w : Fin 4 → ℝ}
    (h : ‖x - Q.centre‖ + ‖w‖ < cubeSide 𝒮 M Q.level) :
    x ∈ Q.strictPts ∧ x + torusProj 4 𝒮.side w ∈ Q.strictPts ∧
      Q.system.embed (x + torusProj 4 𝒮.side w) =
        Q.system.embed x + torusProj 4 Q.system.setting.side w ∧
      supNorm (Q.system.embed x - Q.system.embed (x + torusProj 4 𝒮.side w)) = ‖w‖ ∧
      lOneNorm (Q.system.embed x - Q.system.embed (x + torusProj 4 𝒮.side w)) =
        ∑ μ, |w μ| := by
  have F := H.props
  obtain ⟨p, rfl, hp⟩ := exists_lift_near_centre Q
    (show ‖x - Q.centre‖ < cubeSide 𝒮 M Q.level - ‖w‖ by linarith)
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have hp₁ : p ∈ Q.liftedOpenCube := fun μ => by linarith [hp μ]
  have hp₂ : p + w ∈ Q.liftedOpenCube := fun μ => by
    have e : (p + w) μ - Q.liftedCentre μ = (p μ - Q.liftedCentre μ) + w μ := by
      simp only [Pi.add_apply]
      ring
    have h₁ : |w μ| ≤ ‖w‖ := by simpa using norm_le_pi_norm w μ
    rw [e]
    exact lt_of_le_of_lt (abs_add_le _ _) (by linarith [hp μ])
  have e₁ : torusProj 4 𝒮.side p + torusProj 4 𝒮.side w = torusProj 4 𝒮.side (p + w) :=
    (torusProj_add p w).symm
  have e₂ : p - (p + w) = -w := by abel
  refine ⟨F.cover_bijective.mapsTo hp₁, ?_, F.embed_add p w hp₁ hp₂, ?_, ?_⟩
  · rw [e₁]
    exact F.cover_bijective.mapsTo hp₂
  · rw [e₁, F.embed_cover p hp₁, F.embed_cover _ hp₂, F.local_supLength p hp₁ _ hp₂, e₂,
      norm_neg]
  · rw [e₁, F.embed_cover p hp₁, F.embed_cover _ hp₂, F.local_oneLength p hp₁ _ hp₂]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have e₃ : p μ - (p + w) μ = -w μ := by
      simp only [Pi.add_apply]
      ring
    rw [e₃, abs_neg]
theorem mem_strictPts_of_near {x : 𝒮.Point}
    (h : ‖x - Q.centre‖ < cubeSide 𝒮 M Q.level) : x ∈ Q.strictPts := by apply _root_.YangMills.Construction.PartitionCubes.CubeTorusAveraging.mem_strictPts_of_norm_lt <;> assumption
theorem embed_injOn_strictPts (H : WellPlaced Q) : InjOn Q.system.embed Q.strictPts :=
  H.props.embed_bijective.injOn
theorem image_fine_sites (H : WellPlaced Q) :
    Q.system.embed '' ((spacingLattice 4 𝒮.side 𝒮.ξ : Set 𝒮.Point) ∩ Q.strictPts) =
      (spacingLattice 4 Q.system.setting.side Q.system.setting.ξ :
          Set Q.system.setting.Point) ∩
        Q.localProj '' Q.liftedOpenCube := by
  have E := H.props.embed_sites 0 (Or.inl (Nat.zero_le _))
  have h0 : 𝒮.scale 0 = 𝒮.ξ := by simp [RegionSequence.NestedRegions.scale, scaleSpacing]
  rw [h0] at E
  rw [H.ξ_eq]
  exact E
theorem coe_mapSite (H : WellPlaced Q) (x : 𝒮.FineSite) (hx : (x : 𝒮.Point) ∈ Q.strictPts) :
    ((Q.system.mapSite x : Q.system.setting.FineSite) : Q.system.setting.Point) =
      Q.system.embed x := by
  have hm : Q.system.embed x ∈ spacingLattice 4 Q.system.setting.side Q.system.setting.ξ := by
    have h2 : Q.system.embed x ∈ Q.system.embed ''
        ((spacingLattice 4 𝒮.side 𝒮.ξ : Set 𝒮.Point) ∩ Q.strictPts) := ⟨x, ⟨x.2, hx⟩, rfl⟩
    rw [image_fine_sites H] at h2
    exact h2.1
  exact Classical.epsilon_spec
    (p := fun y : Q.system.setting.FineSite =>
      (y : Q.system.setting.Point) = Q.system.embed x)
    ⟨⟨_, hm⟩, rfl⟩
theorem mem_lattice_of_embed_eq (H : WellPlaced Q) {x : 𝒮.Point} (hx : x ∈ Q.strictPts)
    (y : Q.system.setting.FineSite) (hy : Q.system.embed x = y) :
    x ∈ spacingLattice 4 𝒮.side 𝒮.ξ := by
  have h : (y : Q.system.setting.Point) ∈ Q.system.embed ''
      ((spacingLattice 4 𝒮.side 𝒮.ξ : Set 𝒮.Point) ∩ Q.strictPts) := by
    rw [image_fine_sites H]
    exact ⟨y.2, hy ▸ H.props.embed_bijective.mapsTo hx⟩
  obtain ⟨u, ⟨hu, hu'⟩, hue⟩ := h
  have : u = x := embed_injOn_strictPts H hu' hx (hue.trans hy.symm)
  exact this ▸ hu
theorem coe_unitStep (𝒯 : NestedRegions) (ν : Fin 4) :
    ((unitStep 4 𝒯.side 𝒯.ξ ν : 𝒯.FineSite) : 𝒯.Point) =
      torusProj 4 𝒯.side (Pi.single ν 𝒯.ξ) := rfl
theorem coe_local_unitStep (H : WellPlaced Q) (ν : Fin 4) :
    ((unitStep 4 Q.system.setting.side Q.system.setting.ξ ν : Q.system.setting.FineSite) :
      Q.system.setting.Point) = torusProj 4 Q.system.setting.side (Pi.single ν 𝒮.ξ) := by
  rw [coe_unitStep, H.ξ_eq]
theorem mapSite_add_step (H : WellPlaced Q) (t : 𝒮.FineSite) (ν : Fin 4)
    (h : ‖(t : 𝒮.Point) - Q.centre‖ + 𝒮.ξ < cubeSide 𝒮 M Q.level) :
    Q.system.mapSite (t + unitStep 4 𝒮.side 𝒮.ξ ν) =
      Q.system.mapSite t + unitStep 4 Q.system.setting.side Q.system.setting.ξ ν := by
  have hw : ‖(t : 𝒮.Point) - Q.centre‖ + ‖(Pi.single ν 𝒮.ξ : Fin 4 → ℝ)‖ <
      cubeSide 𝒮 M Q.level := by rwa [norm_pi_single_of_nonneg 𝒮.ξ_pos.le]
  obtain ⟨h₁, h₂, h₃, -, -⟩ := translate_short H hw
  apply Subtype.ext
  rw [coe_mapSite H _ h₂, AddSubgroup.coe_add, AddSubgroup.coe_add, coe_mapSite H _ h₁,
    coe_unitStep 𝒮, coe_unitStep Q.system.setting, H.ξ_eq]
  exact h₃
theorem mapSite_sub_step (H : WellPlaced Q) (t : 𝒮.FineSite) (ν : Fin 4)
    (h : ‖(t : 𝒮.Point) - Q.centre‖ + 𝒮.ξ < cubeSide 𝒮 M Q.level) :
    Q.system.mapSite (t - unitStep 4 𝒮.side 𝒮.ξ ν) =
      Q.system.mapSite t - unitStep 4 Q.system.setting.side Q.system.setting.ξ ν := by
  have hw : ‖(t : 𝒮.Point) - Q.centre‖ + ‖-(Pi.single ν 𝒮.ξ : Fin 4 → ℝ)‖ <
      cubeSide 𝒮 M Q.level := by rwa [norm_neg, norm_pi_single_of_nonneg 𝒮.ξ_pos.le]
  obtain ⟨h₁, h₂, h₃, -, -⟩ := translate_short H hw
  rw [torusProj_neg, ← sub_eq_add_neg, torusProj_neg, ← sub_eq_add_neg] at h₃
  rw [torusProj_neg, ← sub_eq_add_neg] at h₂
  apply Subtype.ext
  rw [coe_mapSite H _ h₂, AddSubgroup.coe_sub, AddSubgroup.coe_sub, coe_mapSite H _ h₁,
    coe_unitStep 𝒮, coe_unitStep Q.system.setting, H.ξ_eq]
  exact h₃
theorem exists_preimage_near (H : WellPlaced Q) {x : 𝒮.Point}
    (hx : ‖x - Q.centre‖ < 5 / 6 * cubeSide 𝒮 M Q.level) (y : Q.system.setting.Point)
    (hy : ‖Q.system.embed x - y‖ ≤ 1 / 6 * cubeSide 𝒮 M Q.level) :
    ∃ x' ∈ Q.strictPts, Q.system.embed x' = y ∧
      lOneNorm (x - x') ≤ lOneNorm (Q.system.embed x - y) := by
  obtain ⟨u, hu, hu'⟩ := exists_proj_eq_abs_eq_norm (Q.system.embed x - y)
  have hun : ‖u‖ = ‖Q.system.embed x - y‖ := by
    rw [← supNorm_eq_norm, show supNorm (Q.system.embed x - y) = ‖u‖ from ?_]
    have hbdd : BddBelow {r | ∃ v : Fin 4 → ℝ,
        torusProj 4 Q.system.setting.side v = Q.system.embed x - y ∧ r = ‖v‖} :=
      ⟨0, by rintro _ ⟨v, -, rfl⟩; exact norm_nonneg v⟩
    refine le_antisymm (csInf_le hbdd ⟨u, hu, rfl⟩) ?_
    rw [supNorm_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ => ?_
    rw [Real.norm_eq_abs, hu']
    exact norm_le_pi_norm _ μ
  have hw : ‖x - Q.centre‖ + ‖-u‖ < cubeSide 𝒮 M Q.level := by
    rw [norm_neg, hun]
    linarith
  obtain ⟨-, h₂, h₃, -, -⟩ := translate_short H hw
  refine ⟨_, h₂, ?_, ?_⟩
  · rw [h₃, torusProj_neg, hu]
    abel
  · have e : x - (x + torusProj 4 𝒮.side (-u)) = torusProj 4 𝒮.side u := by
      rw [torusProj_neg]
      abel
    rw [e, lOneNorm_eq_sum_norm, lOneNorm_eq_sum_norm]
    refine Finset.sum_le_sum fun μ _ => ?_
    rw [← hu']
    exact TorusMetric.addCircle_norm_coe_le_abs (u μ)
theorem mem_strictPts_of_mem_supp (H : WellPlaced Q) {x : 𝒮.Point} (hx : x ∈ Q.supp) :
    x ∈ Q.strictPts :=
  mem_strictPts_of_near (by have := H.supp_near x hx; have := H.side_pos; linarith)
theorem transferFn_embed (H : WellPlaced Q) {x : 𝒮.Point} (hx : x ∈ Q.strictPts) :
    Q.system.transferFn Q.partitionFn (Q.system.embed x) = Q.partitionFn x := by
  unfold CubeSystem.transferFn
  by_cases hs : x ∈ tsupport Q.partitionFn
  · have e : {x' : 𝒮.Point | x' ∈ tsupport Q.partitionFn ∧
        Q.system.embed x' = Q.system.embed x} = {x} := by
      ext x'
      constructor
      · rintro ⟨h₁, h₂⟩
        exact embed_injOn_strictPts H (mem_strictPts_of_mem_supp H h₁) hx h₂
      · rintro rfl
        exact ⟨hs, rfl⟩
    rw [e, finsum_mem_singleton]
  · have e : {x' : 𝒮.Point | x' ∈ tsupport Q.partitionFn ∧
        Q.system.embed x' = Q.system.embed x} = ∅ := by
      refine eq_empty_iff_forall_notMem.2 ?_
      rintro x' ⟨h₁, h₂⟩
      exact hs (embed_injOn_strictPts H (mem_strictPts_of_mem_supp H h₁) hx h₂ ▸ h₁)
    rw [e, finsum_mem_empty, image_eq_zero_of_notMem_tsupport hs]
theorem exists_of_transferFn_ne_zero (y : Q.system.setting.Point)
    (hy : Q.system.transferFn Q.partitionFn y ≠ 0) :
    ∃ x ∈ Q.supp, Q.system.embed x = y := by
  by_contra hn
  apply hy
  unfold CubeSystem.transferFn
  have e : {x : 𝒮.Point | x ∈ tsupport Q.partitionFn ∧ Q.system.embed x = y} = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x hx => hn ⟨x, hx.1, hx.2⟩
  rw [e, finsum_mem_empty]
theorem lOneNorm_sub_comm {S : ℝ} (a b : PeriodicTorus 4 S) :
    lOneNorm (a - b) = lOneNorm (b - a) := by
  rw [lOneNorm_eq_sum_norm, lOneNorm_eq_sum_norm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  exact norm_sub_rev (a μ) (b μ)
theorem transferFn_lipschitz (H : WellPlaced Q) {c r : ℝ}
    (hb : CubeGeometry.IsScaleBounded (𝒮 := 𝒮) c r Q.partitionFn) :
    IsLipschitzAtScale Q.level (c * r⁻¹) (Q.system.transferFn Q.partitionFn) := by
  have hκ : 0 ≤ c * r⁻¹ :=
    (abs_nonneg _).trans (hb.difference (forwardDiff 0) ⟨0, Or.inl rfl⟩ 0)
  have key : ∀ a b : Q.system.setting.Point, Q.system.transferFn Q.partitionFn a ≠ 0 →
      ‖a - b‖ ≤ 1 / 6 * cubeSide 𝒮 M Q.level →
      |Q.system.transferFn Q.partitionFn a - Q.system.transferFn Q.partitionFn b| ≤
        c * r⁻¹ * lOneNorm (a - b) := by
    intro a b ha hab
    obtain ⟨x, hx, rfl⟩ := exists_of_transferFn_ne_zero a ha
    obtain ⟨x', h₁, rfl, h₃⟩ := exists_preimage_near H (H.supp_near x hx) b hab
    rw [transferFn_embed H (mem_strictPts_of_mem_supp H hx), transferFn_embed H h₁]
    exact (hb.lipschitz x x').trans (mul_le_mul_of_nonneg_left h₃ hκ)
  intro y y' hyy
  rw [supNorm_eq_norm] at hyy
  have hyy' : ‖y - y'‖ ≤ 1 / 6 * cubeSide 𝒮 M Q.level := hyy.trans H.local_ball_le
  by_cases h₁ : Q.system.transferFn Q.partitionFn y = 0
  · by_cases h₂ : Q.system.transferFn Q.partitionFn y' = 0
    · rw [h₁, h₂, sub_self, abs_zero, lOneNorm_eq_sum_norm]
      exact mul_nonneg hκ (Finset.sum_nonneg fun μ _ => norm_nonneg _)
    · have h₃ := key y' y h₂ (by rwa [norm_sub_rev])
      rwa [abs_sub_comm, lOneNorm_sub_comm] at h₃
  · exact key y y' h₁ hyy'
theorem backward_forward_diff_eq {S ξ : ℝ} (f : LatticeSite 4 S ξ → ℝ) (x : LatticeSite 4 S ξ)
    (μ : Fin 4) :
    backwardDiff μ (forwardDiff μ f) x =
      ξ⁻¹ * (ξ⁻¹ * (f x - f (x - unitStep 4 S ξ μ)) -
        ξ⁻¹ * (f (x + unitStep 4 S ξ μ) - f x)) := by
  simp only [backwardDiff, forwardDiff, sub_add_cancel]
theorem abs_second_diff_transferFn_le (H : WellPlaced Q) {c r : ℝ}
    (hb : CubeGeometry.IsScaleBounded (𝒮 := 𝒮) c r Q.partitionFn)
    (x : Q.system.setting.FineSite) (μ : Fin 4) :
    |backwardDiff μ (forwardDiff μ (onSites (Q.system.transferFn Q.partitionFn))) x| ≤
      c * r⁻¹ ^ 2 := by
  have hC : 0 ≤ c * r⁻¹ ^ 2 := (abs_nonneg _).trans
    (hb.second_difference (backwardDiff 0) (forwardDiff 0) ⟨0, Or.inr rfl⟩ ⟨0, Or.inl rfl⟩ 0)
  have hsame := H.ξ_eq
  have hstep := H.step_le
  have hξ := 𝒮.ξ_pos
  by_cases hA : ∃ s : 𝒮.FineSite, ‖(s : 𝒮.Point) - Q.centre‖ <
      5 / 6 * cubeSide 𝒮 M Q.level + 𝒮.ξ ∧ Q.system.embed (s : 𝒮.Point) = x
  · obtain ⟨s, hs, hsx⟩ := hA
    have hw₁ : ‖(s : 𝒮.Point) - Q.centre‖ + ‖(Pi.single μ 𝒮.ξ : Fin 4 → ℝ)‖ <
        cubeSide 𝒮 M Q.level := by
      rw [norm_pi_single_of_nonneg hξ.le]
      linarith
    have hw₂ : ‖(s : 𝒮.Point) - Q.centre‖ + ‖-(Pi.single μ 𝒮.ξ : Fin 4 → ℝ)‖ <
        cubeSide 𝒮 M Q.level := by
      rw [norm_neg, norm_pi_single_of_nonneg hξ.le]
      linarith
    obtain ⟨i₀, i₁, t₁, -, -⟩ := translate_short H hw₁
    obtain ⟨-, i₂, t₂, -, -⟩ := translate_short H hw₂
    rw [torusProj_neg, ← sub_eq_add_neg, torusProj_neg, ← sub_eq_add_neg] at t₂
    rw [torusProj_neg, ← sub_eq_add_neg] at i₂
    have e₀ : onSites (Q.system.transferFn Q.partitionFn) x =
        CubeGeometry.restrictToFine Q.partitionFn s := by
      change Q.system.transferFn Q.partitionFn (x : Q.system.setting.Point) = Q.partitionFn s
      rw [← hsx, transferFn_embed H i₀]
    have e₁ : onSites (Q.system.transferFn Q.partitionFn)
        (x + unitStep 4 Q.system.setting.side Q.system.setting.ξ μ) =
        CubeGeometry.restrictToFine Q.partitionFn (s + unitStep 4 𝒮.side 𝒮.ξ μ) := by
      change Q.system.transferFn Q.partitionFn ((x : Q.system.setting.Point) +
        ((unitStep 4 Q.system.setting.side Q.system.setting.ξ μ :
            Q.system.setting.FineSite) : Q.system.setting.Point)) =
          Q.partitionFn ((s : 𝒮.Point) + torusProj 4 𝒮.side (Pi.single μ 𝒮.ξ))
      rw [coe_local_unitStep H μ, ← hsx, ← t₁, transferFn_embed H i₁]
    have e₂ : onSites (Q.system.transferFn Q.partitionFn)
        (x - unitStep 4 Q.system.setting.side Q.system.setting.ξ μ) =
        CubeGeometry.restrictToFine Q.partitionFn (s - unitStep 4 𝒮.side 𝒮.ξ μ) := by
      change Q.system.transferFn Q.partitionFn ((x : Q.system.setting.Point) -
        ((unitStep 4 Q.system.setting.side Q.system.setting.ξ μ :
            Q.system.setting.FineSite) : Q.system.setting.Point)) =
          Q.partitionFn ((s : 𝒮.Point) - torusProj 4 𝒮.side (Pi.single μ 𝒮.ξ))
      rw [coe_local_unitStep H μ, ← hsx, ← t₂, transferFn_embed H i₂]
    have key := hb.second_difference (backwardDiff μ) (forwardDiff μ) ⟨μ, Or.inr rfl⟩
      ⟨μ, Or.inl rfl⟩ s
    rw [backward_forward_diff_eq, e₀, e₁, e₂, hsame, ← backward_forward_diff_eq]
    exact key
  · have zero : ∀ (y : Q.system.setting.FineSite) (w : Fin 4 → ℝ), ‖w‖ ≤ 𝒮.ξ →
        (x : Q.system.setting.Point) = y + torusProj 4 Q.system.setting.side w →
        (∃ u : 𝒮.FineSite, (u : 𝒮.Point) = torusProj 4 𝒮.side w) →
        onSites (Q.system.transferFn Q.partitionFn) y = 0 := by
      rintro y w hw hxy ⟨u, hu⟩
      by_contra hne
      obtain ⟨x₀, h₀, h₀e⟩ := exists_of_transferFn_ne_zero _ hne
      have hs₀ : x₀ ∈ spacingLattice 4 𝒮.side 𝒮.ξ :=
        mem_lattice_of_embed_eq H (mem_strictPts_of_mem_supp H h₀) y h₀e
      have hn := H.supp_near _ h₀
      have hw' : ‖x₀ - Q.centre‖ + ‖w‖ < cubeSide 𝒮 M Q.level := by linarith
      obtain ⟨-, -, t, -, -⟩ := translate_short H hw'
      refine hA ⟨⟨x₀, hs₀⟩ + u, ?_, ?_⟩
      · change ‖x₀ + (u : 𝒮.Point) - Q.centre‖ < _
        rw [hu, add_sub_right_comm]
        calc ‖x₀ - Q.centre + torusProj 4 𝒮.side w‖ ≤
              ‖x₀ - Q.centre‖ + ‖torusProj 4 𝒮.side w‖ :=
              norm_add_le _ _
          _ < _ := by linarith [norm_torusProj_le (S := 𝒮.side) w]
      · change Q.system.embed (x₀ + (u : 𝒮.Point)) = x
        rw [hu, t, h₀e, hxy]
    have z₀ := zero x 0 (by simpa using hξ.le) (by
      have : torusProj 4 Q.system.setting.side (0 : Fin 4 → ℝ) = 0 := by
        funext ν
        simp [torusProj]
      rw [this, add_zero]) ⟨0, by
        funext ν
        simp [torusProj]⟩
    have z₁ := zero (x + unitStep 4 Q.system.setting.side Q.system.setting.ξ μ)
      (-(Pi.single μ 𝒮.ξ)) (by rw [norm_neg, norm_pi_single_of_nonneg hξ.le]) (by
        rw [AddSubgroup.coe_add, coe_local_unitStep H μ, torusProj_neg]
        abel) ⟨-unitStep 4 𝒮.side 𝒮.ξ μ, by
          rw [AddSubgroup.coe_neg, coe_unitStep, torusProj_neg]⟩
    have z₂ := zero (x - unitStep 4 Q.system.setting.side Q.system.setting.ξ μ)
      (Pi.single μ 𝒮.ξ) (by rw [norm_pi_single_of_nonneg hξ.le]) (by
        rw [AddSubgroup.coe_sub, coe_local_unitStep H μ]
        abel) ⟨unitStep 4 𝒮.side 𝒮.ξ μ, coe_unitStep 𝒮 μ⟩
    have e : Q.system.setting.ξ⁻¹ * (Q.system.setting.ξ⁻¹ * ((0 : ℝ) - 0) -
        Q.system.setting.ξ⁻¹ * (0 - 0)) = 0 := by ring
    rw [backward_forward_diff_eq, z₀, z₁, z₂, e, abs_zero]
    exact hC
theorem abs_laplacian_transferFn_le (H : WellPlaced Q) {c r : ℝ}
    (hb : CubeGeometry.IsScaleBounded (𝒮 := 𝒮) c r Q.partitionFn)
    (x : Q.system.setting.FineSite) :
    |latticeLaplacian (onSites (Q.system.transferFn Q.partitionFn)) x| ≤
      4 * (c * r⁻¹ ^ 2) := by
  have e : latticeLaplacian (onSites (Q.system.transferFn Q.partitionFn)) x =
      ∑ μ, backwardDiff μ (forwardDiff μ (onSites (Q.system.transferFn Q.partitionFn))) x :=
    rfl
  rw [e]
  calc |∑ μ, backwardDiff μ (forwardDiff μ (onSites (Q.system.transferFn Q.partitionFn))) x|
      ≤ ∑ μ, |backwardDiff μ (forwardDiff μ (onSites (Q.system.transferFn Q.partitionFn))) x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _μ : Fin 4, c * r⁻¹ ^ 2 :=
        Finset.sum_le_sum fun μ _ => abs_second_diff_transferFn_le H hb x μ
    _ = 4 * (c * r⁻¹ ^ 2) := by simp
theorem partitionTransfers (H : WellPlaced Q) : Q.PartitionTransfers :=
  ⟨fun _ hx => transferFn_embed H hx, exists_of_transferFn_ne_zero,
    fun _ _ hb => transferFn_lipschitz H hb, fun _ _ hb x => abs_laplacian_transferFn_le H hb x⟩
end PartitionCubes.TorusTransfer
end YangMills.Construction
