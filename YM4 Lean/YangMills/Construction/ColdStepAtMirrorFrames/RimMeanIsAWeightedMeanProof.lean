import YangMills.Construction.ColdStepAtMirrorFrames.RimMeanIsAWeightedMean
import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
theorem cutoffMeanIsGibbsMean_of_cutoffFactorIsRadialCutoff (hRadial : CutoffFactorIsRadialCutoff) :
    CutoffMeanIsGibbsMean := by
  intro F ρ p hρ hp
  have hcut := hRadial ρ p hρ hp
  set r : ℝ → ℝ := fun u => cutoffFactor ρ p (max u 0) with hr
  have hrc : Continuous r := hcut.smooth.continuous
  have hfac : ∀ η : StepVariable (finiteCells F), ∀ e, cutoffFactor ρ p ‖η e‖ = r ‖η e‖ := fun η e => by
    simp [hr, max_eq_left (norm_nonneg (η e))]
  have hcont : Continuous (cutoffWeight (F := F) ρ p) := by
    have : cutoffWeight (F := F) ρ p = fun η => ∏ e, r ‖η e‖ := by
      funext η
      simp only [cutoffWeight, hfac]
    rw [this]
    exact continuous_finset_prod _ fun e _ => hrc.comp (continuous_apply e).norm
  have hnn : ∀ u : ℝ, 0 ≤ cutoffFactor ρ p u := fun u => by
    unfold cutoffFactor
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hnonneg : ∀ η : StepVariable (finiteCells F), 0 ≤ cutoffWeight ρ p η := fun η =>
    Finset.prod_nonneg fun e _ => hnn _
  have hsupp : ∀ η : StepVariable (finiteCells F), cutoffWeight ρ p η ≠ 0 → ∀ e, ‖η e‖ < ρ := fun η hη e => by
    by_contra he
    exact hη (Finset.prod_eq_zero (Finset.mem_univ e) (by simp [cutoffFactor, he]))
  have hK : IsCompact {η : StepVariable (finiteCells F) | ∀ e, ‖η e‖ ≤ ρ} := by
    have : {η : StepVariable (finiteCells F) | ∀ e, ‖η e‖ ≤ ρ} =
        Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
      ext η
      simp
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hcs : HasCompactSupport (cutoffWeight (F := F) ρ p) :=
    HasCompactSupport.intro hK fun η hη => by
      by_contra h
      exact hη fun e => (hsupp η h e).le
  have hint : Integrable (cutoffWeight (F := F) ρ p) := hcont.integrable_of_hasCompactSupport hcs
  have hzero : cutoffWeight (F := F) ρ p 0 ≠ 0 := by
    have h0 : ∀ e : ↥(chordBonds (finiteCells F)),
        cutoffFactor ρ p ‖(0 : StepVariable (finiteCells F)) e‖ = 1 := fun e => by
      rw [hfac]
      simpa using hcut.one 0 le_rfl (by positivity)
    rw [cutoffWeight, Finset.prod_eq_one fun e _ => h0 e]
    exact one_ne_zero
  have hpos : 0 < ∫ η : StepVariable (finiteCells F), cutoffWeight ρ p η :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnonneg hzero
  have hmeas : Measurable fun η : StepVariable (finiteCells F) => ENNReal.ofReal (cutoffWeight ρ p η) :=
    hcont.measurable.ennreal_ofReal
  refine ⟨isFiniteMeasure_withDensity_ofReal hint.2, ?_, ?_, fun Ψ H => ?_⟩
  · intro h0
    have h1 := (withDensity_eq_zero_iff hmeas.aemeasurable).mp h0
    have h2 : cutoffWeight (F := F) ρ p =ᵐ[volume] 0 := by
      filter_upwards [h1] with η hη
      have := ENNReal.ofReal_eq_zero.mp hη
      exact le_antisymm this (hnonneg η)
    rw [integral_congr_ae h2] at hpos
    simp at hpos
  · rw [cutoffLaw, ae_withDensity_iff hmeas]
    refine Filter.Eventually.of_forall fun η hη => hsupp η fun h => hη (by simp [h])
  · have key : ∀ g : StepVariable (finiteCells F) → ℝ,
        ∫ η, g η ∂cutoffLaw F ρ p = ∫ η, cutoffWeight ρ p η * g η := fun g => by
      rw [cutoffLaw, integral_withDensity_eq_integral_toReal_smul hmeas
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun η => ?_
      simp [ENNReal.toReal_ofReal (hnonneg η)]
    unfold cutoffMean gibbsMean
    rw [key, key]
    congr 1
    · apply integral_congr_ae
      refine Filter.Eventually.of_forall fun η => ?_
      simp only
      ring
end YangMills.Construction.ColdStepAtMirrorFrames
end
