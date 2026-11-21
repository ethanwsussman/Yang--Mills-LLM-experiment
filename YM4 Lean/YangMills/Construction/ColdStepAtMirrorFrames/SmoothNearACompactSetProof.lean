import YangMills.Construction.ColdStepAtMirrorFrames.SmoothNearACompactSet
import Mathlib
set_option autoImplicit false
noncomputable section
open Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem uniformDerivBoundNearCompactOfContinuous_holds :
    UniformDerivBoundNearCompactOfContinuous := by
  intro n X _ _ F S hS hF
  set W : Set ((Fin n → ℝ) × X) := {p | ContDiffAt ℝ 3 F p} with hW
  have hWopen : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    exact (show ContDiffAt ℝ 3 F p from hp).eventually (by simp)
  have hFW : ContDiffOn ℝ 3 F W := fun p hp => (show ContDiffAt ℝ 3 F p from hp).contDiffWithinAt
  have hzeroW : ({0} : Set (Fin n → ℝ)) ×ˢ S ⊆ W := by
    rintro ⟨t, q⟩ ⟨ht, hq⟩
    obtain rfl : t = 0 := ht
    exact hF q hq
  obtain ⟨a, b, ha, hb, h0a, hSb, habW⟩ :=
    generalized_tube_lemma isCompact_singleton hS hWopen hzeroW
  obtain ⟨ρ, hρ, hballa⟩ := Metric.isOpen_iff.mp ha 0 (h0a rfl)
  set δ : ℝ := ρ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hclosed : Metric.closedBall (0 : Fin n → ℝ) δ ⊆ a := fun p hp =>
    hballa (lt_of_le_of_lt (Metric.mem_closedBall.mp hp) (by rw [hδ]; linarith))
  have hcpt : IsCompact (Metric.closedBall (0 : Fin n → ℝ) δ ×ˢ S) :=
    (isCompact_closedBall _ _).prod hS
  have hcptW : Metric.closedBall (0 : Fin n → ℝ) δ ×ˢ S ⊆ W := fun p hp =>
    habW ⟨hclosed hp.1, hSb hp.2⟩
  have hbound : ∀ m, m ≤ 3 → ∃ B : ℝ, ∀ p ∈ Metric.closedBall (0 : Fin n → ℝ) δ ×ˢ S,
      ‖iteratedFDeriv ℝ m F p‖ ≤ B := fun m hm => by
    have hcont : ContinuousOn (iteratedFDeriv ℝ m F) W :=
      (hFW.continuousOn_iteratedFDerivWithin (m := m) (by exact_mod_cast hm)
        hWopen.uniqueDiffOn).congr (fun p hp => (iteratedFDerivWithin_of_isOpen m hWopen hp).symm)
    exact hcpt.exists_bound_of_continuousOn (hcont.mono hcptW)
  choose! B hB using hbound
  refine ⟨δ, ∑ m ∈ Finset.range 4, |B m|, hδpos, fun t ht q hq => ?_, fun q hq => ?_⟩
  · have hp : (t, q) ∈ W := hcptW ⟨Metric.ball_subset_closedBall ht, hq⟩
    have hcont : ContinuousAt F (t, q) := (show ContDiffAt ℝ 3 F (t, q) from hp).continuousAt
    have hpair : ContinuousAt (fun q' : X => (t, q')) q := by fun_prop
    exact (ContinuousAt.comp (f := fun q' : X => (t, q')) hcont hpair).continuousWithinAt
  set L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) × X := ContinuousLinearMap.inl ℝ _ _ with hL
  set g : (Fin n → ℝ) × X → ℝ := fun p => F (p + (0, q)) with hg
  set V : Set ((Fin n → ℝ) × X) := (fun p => p + ((0 : Fin n → ℝ), q)) ⁻¹' W with hV
  have hVopen : IsOpen V := hWopen.preimage (continuous_add_const _)
  have hgV : ContDiffOn ℝ 3 g V :=
    hFW.comp (contDiff_id.add contDiff_const).contDiffOn (fun p hp => hp)
  have hfiber : (fun t => F (t, q)) = g ∘ L := by
    funext t
    simp [hg, hL]
  have hLV : ∀ t ∈ Metric.ball (0 : Fin n → ℝ) δ, L t ∈ V := fun t ht => by
    have : (t, q) ∈ Metric.closedBall (0 : Fin n → ℝ) δ ×ˢ S :=
      ⟨Metric.ball_subset_closedBall ht, hq⟩
    have hin := hcptW this
    simpa [hV, hL] using hin
  constructor
  · rw [hfiber]
    exact hgV.comp L.contDiff.contDiffOn hLV
  · intro m hm t ht
    have hcomp := L.iteratedFDerivWithin_comp_right hgV hVopen.uniqueDiffOn
      (hVopen.preimage L.continuous).uniqueDiffOn (hLV t ht) (i := m) (by exact_mod_cast hm)
    rw [iteratedFDerivWithin_of_isOpen m (hVopen.preimage L.continuous) (hLV t ht),
      iteratedFDerivWithin_of_isOpen m hVopen (hLV t ht)] at hcomp
    rw [hfiber, hcomp]
    have hshift : iteratedFDeriv ℝ m g (L t) = iteratedFDeriv ℝ m F (L t + (0, q)) := by
      rw [hg]
      exact iteratedFDeriv_comp_add_right m (0, q) (L t)
    have hmemcpt : L t + ((0 : Fin n → ℝ), q) ∈ Metric.closedBall (0 : Fin n → ℝ) δ ×ˢ S := by
      simpa [hL] using (⟨Metric.ball_subset_closedBall ht, hq⟩ :
        (t, q) ∈ Metric.closedBall (0 : Fin n → ℝ) δ ×ˢ S)
    have hLnorm : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one ℝ _ _
    have hcompnorm := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ m g (L t)) (fun _ => L)
    have hprodle : ∏ _i : Fin m, ‖L‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hLnorm)
    calc ‖(iteratedFDeriv ℝ m g (L t)).compContinuousLinearMap fun _ => L‖
        ≤ ‖iteratedFDeriv ℝ m g (L t)‖ * ∏ _i : Fin m, ‖L‖ := hcompnorm
      _ ≤ ‖iteratedFDeriv ℝ m g (L t)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprodle (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ m F (L t + (0, q))‖ := by rw [mul_one, hshift]
      _ ≤ B m := hB m hm _ hmemcpt
      _ ≤ |B m| := le_abs_self _
      _ ≤ ∑ m ∈ Finset.range 4, |B m| :=
        Finset.single_le_sum (f := fun m => |B m|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))
end YangMills.Construction.ColdStepAtMirrorFrames
end
