import YangMills.Construction.ResponseInTheExpansion.DominatedOnTheBallsAtOrderTwo
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
namespace YangMills.Construction.LinearResponse
open YangMills.Construction.ColdStepAtMirrorFrames
private theorem contDiff_slice_bounded_near_compact (k : ℕ) (Q : Type) [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (G : (Fin k → ℝ) × Q → ℝ) (K : Set Q)
    (hK : IsCompact K) (hG : ∀ η ∈ K, ContDiffAt ℝ 2 G (0, η)) :
    ∃ r M : ℝ, 0 < r ∧
      (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ContinuousOn (fun η => G (τ, η)) K) ∧
      ∀ η ∈ K, ContDiffOn ℝ 2 (fun τ => G (τ, η)) (Metric.ball 0 r) ∧
        ∀ j, j ≤ 2 → ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r,
          ‖iteratedFDeriv ℝ j (fun τ => G (τ, η)) τ‖ ≤ M := by
  set U : Set ((Fin k → ℝ) × Q) := {z | ContDiffAt ℝ 2 G z} with hU
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact (show ContDiffAt ℝ 2 G z from hz).eventually (by simp)
  have hGU : ContDiffOn ℝ 2 G U := fun z hz => (show ContDiffAt ℝ 2 G z from hz).contDiffWithinAt
  have hsub : ({0} : Set (Fin k → ℝ)) ×ˢ K ⊆ U := by
    rintro ⟨t, η⟩ ⟨ht, hη⟩
    obtain rfl : t = 0 := ht
    exact hG η hη
  obtain ⟨u, v, hu, hv, h0u, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hK hUo hsub
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp hu 0 (h0u rfl)
  set r : ℝ := r₀ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hcb : Metric.closedBall (0 : Fin k → ℝ) r ⊆ u := fun z hz =>
    hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by rw [hr]; linarith))
  have hC : IsCompact (Metric.closedBall (0 : Fin k → ℝ) r ×ˢ K) :=
    (isCompact_closedBall _ _).prod hK
  have hCU : Metric.closedBall (0 : Fin k → ℝ) r ×ˢ K ⊆ U := fun z hz =>
    huv ⟨hcb hz.1, hKv hz.2⟩
  have hbd : ∀ j, j ≤ 2 → ∃ M : ℝ, ∀ z ∈ Metric.closedBall (0 : Fin k → ℝ) r ×ˢ K,
      ‖iteratedFDeriv ℝ j G z‖ ≤ M := fun j hj => by
    have hc : ContinuousOn (iteratedFDeriv ℝ j G) U :=
      (hGU.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj)
        hUo.uniqueDiffOn).congr (fun z hz => (iteratedFDerivWithin_of_isOpen j hUo hz).symm)
    exact hC.exists_bound_of_continuousOn (hc.mono hCU)
  choose! Mj hMj using hbd
  refine ⟨r, ∑ j ∈ Finset.range 3, |Mj j|, hrpos, fun τ hτ η hη => ?_, fun η hη => ?_⟩
  · have hz : (τ, η) ∈ U := hCU ⟨Metric.ball_subset_closedBall hτ, hη⟩
    have hc : ContinuousAt G (τ, η) := (show ContDiffAt ℝ 2 G (τ, η) from hz).continuousAt
    have h2 : ContinuousAt (fun η' : Q => (τ, η')) η := by fun_prop
    exact (ContinuousAt.comp (f := fun η' : Q => (τ, η')) hc h2).continuousWithinAt
  set ι : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) × Q := ContinuousLinearMap.inl ℝ _ _ with hι
  set f : (Fin k → ℝ) × Q → ℝ := fun z => G (z + (0, η)) with hf
  set s : Set ((Fin k → ℝ) × Q) := (fun z => z + ((0 : Fin k → ℝ), η)) ⁻¹' U with hs
  have hso : IsOpen s := hUo.preimage (continuous_add_const _)
  have hfs : ContDiffOn ℝ 2 f s :=
    hGU.comp (contDiff_id.add contDiff_const).contDiffOn (fun z hz => hz)
  have hslice : (fun τ => G (τ, η)) = f ∘ ι := by
    funext τ
    simp [hf, hι]
  have hiota : ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ι τ ∈ s := fun τ hτ => by
    have : (τ, η) ∈ Metric.closedBall (0 : Fin k → ℝ) r ×ˢ K :=
      ⟨Metric.ball_subset_closedBall hτ, hη⟩
    have h2 := hCU this
    simpa [hs, hι] using h2
  constructor
  · rw [hslice]
    exact hfs.comp ι.contDiff.contDiffOn hiota
  · intro j hj τ hτ
    have hcomp := ι.iteratedFDerivWithin_comp_right hfs hso.uniqueDiffOn
      (hso.preimage ι.continuous).uniqueDiffOn (hiota τ hτ) (i := j) (by exact_mod_cast hj)
    rw [iteratedFDerivWithin_of_isOpen j (hso.preimage ι.continuous) (hiota τ hτ),
      iteratedFDerivWithin_of_isOpen j hso (hiota τ hτ)] at hcomp
    rw [hslice, hcomp]
    have hadd : iteratedFDeriv ℝ j f (ι τ) = iteratedFDeriv ℝ j G (ι τ + (0, η)) := by
      rw [hf]
      exact iteratedFDeriv_comp_add_right j (0, η) (ι τ)
    have hmem : ι τ + ((0 : Fin k → ℝ), η) ∈ Metric.closedBall (0 : Fin k → ℝ) r ×ˢ K := by
      simpa [hι] using (⟨Metric.ball_subset_closedBall hτ, hη⟩ :
        (τ, η) ∈ Metric.closedBall (0 : Fin k → ℝ) r ×ˢ K)
    have hnorm : ‖ι‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one ℝ _ _
    have h3 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ j f (ι τ)) (fun _ => ι)
    have hprod : ∏ _i : Fin j, ‖ι‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hnorm)
    calc ‖(iteratedFDeriv ℝ j f (ι τ)).compContinuousLinearMap fun _ => ι‖
        ≤ ‖iteratedFDeriv ℝ j f (ι τ)‖ * ∏ _i : Fin j, ‖ι‖ := h3
      _ ≤ ‖iteratedFDeriv ℝ j f (ι τ)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ j G (ι τ + (0, η))‖ := by rw [mul_one, hadd]
      _ ≤ Mj j := hMj j hj _ hmem
      _ ≤ |Mj j| := le_abs_self _
      _ ≤ ∑ j ∈ Finset.range 3, |Mj j| :=
        Finset.single_le_sum (f := fun j => |Mj j|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))
theorem dominatedOfContDiffTwoOnClosedBalls_holds : DominatedOfContDiffTwoOnClosedBalls := by
  intro ι _ k ρ μ G hμ hG
  set K : Set (BondField ι) := {η | ∀ b, ‖η b‖ ≤ ρ} with hK
  have hcomp : IsCompact K := by
    have : K = Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
      ext η
      simp [hK]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨r, M, hr, hcont, hsm⟩ :=
    contDiff_slice_bounded_near_compact k (BondField ι) G K hcomp fun η hη => hG η hη
  refine ⟨r, M, hr, ⟨fun τ hτ => ?_, ?_, ?_⟩⟩
  · have hm : MeasurableSet K := hcomp.isClosed.measurableSet
    have h1 : AEStronglyMeasurable (fun η => G (τ, η)) (μ.restrict K) :=
      (hcont τ hτ).aestronglyMeasurable hm
    have h2 : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem hμ
    rwa [h2] at h1
  · filter_upwards [hμ] with η hη
    exact (hsm η hη).1
  · filter_upwards [hμ] with η hη
    exact (hsm η hη).2
end YangMills.Construction.LinearResponse
end
