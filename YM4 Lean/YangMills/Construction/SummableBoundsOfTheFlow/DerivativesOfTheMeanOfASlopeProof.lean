import YangMills.Construction.ColdStepAtMirrorFrames.RimOfACut
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfTheMeanOfASlope
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOverASecondMeasure
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Cumulants Estimates TiltedMeans
namespace Cumulants
namespace SlopeMeanDerivatives
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ}
def bondSlopeWeight (p : ℝ → ℝ) (v : BondVector) : ℝ := |deriv p ‖v‖| * (‖v‖⁻¹ * ‖v‖)
def slopeDominator (p : ℝ → ℝ) (η : BondField ι) : ℝ := 1 + ∑ b, bondSlopeWeight p (η b)
theorem bondSlopeWeight_nonneg (v : BondVector) : 0 ≤ bondSlopeWeight p v := by
  unfold bondSlopeWeight
  positivity
theorem one_le_slopeDominator (η : BondField ι) : 1 ≤ slopeDominator p η := by
  unfold slopeDominator
  have : 0 ≤ ∑ b, bondSlopeWeight p (η b) := Finset.sum_nonneg fun b _ => bondSlopeWeight_nonneg _
  linarith
theorem measurable_slopeDominator : Measurable (slopeDominator (ι := ι) p) := by
  unfold slopeDominator bondSlopeWeight
  refine measurable_const.add (Finset.measurable_fun_sum _ fun b _ => ?_)
  have h1 : Measurable fun η : BondField ι => ‖η b‖ := (measurable_pi_apply b).norm
  exact (((measurable_deriv p).comp h1).abs).mul (h1.inv.mul h1)
def radialProfile (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : ℝ := cutoffFactor ρ p (max u 0)
theorem radialProfile_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ radialProfile ρ p u := by
  unfold radialProfile cutoffFactor
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl
theorem bondSlopeWeight_mul_cutoffFactor (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (h : IsRadialCutoff ρ (radialProfile ρ p)) (v : BondVector) :
    bondSlopeWeight p v * cutoffFactor ρ p ‖v‖ = |deriv (radialProfile ρ p) ‖v‖| := by
  by_cases h0 : v = 0
  · subst h0
    have he : radialProfile ρ p =ᶠ[𝓝 0] fun _ => (1 : ℝ) := by
      have hm : Set.Iio (5 * ρ / 8) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by positivity)
      filter_upwards [hm] with u hu
      have h1 := h.one (max u 0) (le_max_right _ _) (max_le (le_of_lt hu) (by positivity))
      have h2 : radialProfile ρ p (max u 0) = radialProfile ρ p u := by
        unfold radialProfile
        simp
      rw [← h2, h1]
    have hd : deriv (radialProfile ρ p) 0 = 0 := by
      rw [he.deriv_eq]
      simp
    simp [bondSlopeWeight, hd]
  · have hu : 0 < ‖v‖ := norm_pos_iff.mpr h0
    by_cases h1 : ‖v‖ < ρ
    · have hpd : HasDerivAt p (deriv p ‖v‖) ‖v‖ := by
        have hs : Set.Ico 0 ρ ∈ 𝓝 ‖v‖ := Ico_mem_nhds hu h1
        exact ((hp.smooth.contDiffAt hs).differentiableAt (by simp)).hasDerivAt
      have hev : radialProfile ρ p =ᶠ[𝓝 ‖v‖] fun u => Real.exp (- p u) := by
        filter_upwards [Ioo_mem_nhds hu h1] with u hu'
        unfold radialProfile cutoffFactor
        rw [max_eq_left hu'.1.le, if_pos hu'.2]
      have hd : HasDerivAt (fun u => Real.exp (- p u)) (Real.exp (- p ‖v‖) * (- deriv p ‖v‖)) ‖v‖ :=
        hpd.neg.exp
      have hd' : deriv (radialProfile ρ p) ‖v‖ = Real.exp (- p ‖v‖) * (- deriv p ‖v‖) :=
        (hd.congr_of_eventuallyEq hev).deriv
      have hc : cutoffFactor ρ p ‖v‖ = Real.exp (- p ‖v‖) := by
        unfold cutoffFactor
        rw [if_pos h1]
      rw [hd', hc, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
      unfold bondSlopeWeight
      rw [inv_mul_cancel₀ hu.ne']
      ring
    · have hz : radialProfile ρ p ‖v‖ = 0 := h.zero _ (not_lt.mp h1)
      have hm : IsLocalMin (radialProfile ρ p) ‖v‖ :=
        Filter.Eventually.of_forall fun u => by rw [hz]; exact radialProfile_nonneg ρ p u
      have hc : cutoffFactor ρ p ‖v‖ = 0 := by
        unfold cutoffFactor
        rw [if_neg h1]
      rw [hm.deriv_eq_zero, hc]
      simp
theorem abs_cutoffSlope_le (e η : BondField ι) :
    |cutoffSlope p e η| ≤ slopeDominator p η * ‖e‖ := by
  unfold cutoffSlope
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ b, |deriv p ‖η b‖ * ‖η b‖⁻¹ * ⟪η b, e b⟫| ≤ bondSlopeWeight p (η b) * ‖e‖ := by
    intro b
    rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    have h2 := abs_real_inner_le_norm (η b) (e b)
    have h3 : ‖e b‖ ≤ ‖e‖ := norm_le_pi_norm e b
    calc |deriv p ‖η b‖| * ‖η b‖⁻¹ * |⟪η b, e b⟫|
        ≤ |deriv p ‖η b‖| * ‖η b‖⁻¹ * (‖η b‖ * ‖e‖) :=
          mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)))
            (by positivity)
      _ = bondSlopeWeight p (η b) * ‖e‖ := by
          unfold bondSlopeWeight
          ring
  refine (Finset.sum_le_sum fun b _ => h1 b).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  unfold slopeDominator
  linarith
def slopeCLM (p : ℝ → ℝ) (η : BondField ι) : BondField ι →L[ℝ] ℝ :=
  ∑ b, (deriv p ‖η b‖ * ‖η b‖⁻¹) •
    (innerSL ℝ (η b)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => BondVector) b)
theorem slopeCLM_apply (p : ℝ → ℝ) (η e : BondField ι) : slopeCLM p η e = cutoffSlope p e η := by
  unfold slopeCLM cutoffSlope
  simp [ContinuousLinearMap.sum_apply]
def normalizedSlopeCLM (p : ℝ → ℝ) (η : BondField ι) : BondField ι →L[ℝ] ℝ :=
  (slopeDominator p η)⁻¹ • slopeCLM p η
theorem slopeDominator_mul_normalizedSlopeCLM (p : ℝ → ℝ) (η e : BondField ι) :
    slopeDominator p η * normalizedSlopeCLM p η e = cutoffSlope p e η := by
  have h := one_le_slopeDominator (p := p) η
  have h0 : slopeDominator p η ≠ 0 := by positivity
  simp only [normalizedSlopeCLM, ContinuousLinearMap.smul_apply, smul_eq_mul, slopeCLM_apply]
  field_simp
theorem norm_normalizedSlopeCLM_le (p : ℝ → ℝ) (η : BondField ι) : ‖normalizedSlopeCLM p η‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun e => ?_
  have h := one_le_slopeDominator (p := p) η
  have hw : 0 < slopeDominator p η := by linarith
  simp only [normalizedSlopeCLM, ContinuousLinearMap.smul_apply, smul_eq_mul, slopeCLM_apply,
    norm_mul, Real.norm_eq_abs, one_mul, abs_inv, abs_of_pos hw]
  rw [inv_mul_le_iff₀ hw]
  exact abs_cutoffSlope_le e η
theorem measurable_cutoffSlope (p : ℝ → ℝ) (e : BondField ι) :
    Measurable (cutoffSlope (ι := ι) p e) := by
  unfold cutoffSlope
  refine Finset.measurable_fun_sum _ fun b _ => ?_
  have h1 : Measurable fun η : BondField ι => ‖η b‖ := (measurable_pi_apply b).norm
  exact (((measurable_deriv p).comp h1).mul h1.inv).mul
    ((measurable_pi_apply b).inner measurable_const)
end SlopeMeanDerivatives
open SlopeMeanDerivatives in
theorem cutoffSlopeMeanDerivFormulas_holds (hGibbs : CutoffMeanIsGibbsMean)
    (hRad : CutoffFactorIsRadialCutoff) (hTilt : TiltedMeanDifferentiation) :
    cutoffSlopeMeanDerivFormulas := by
  classical
  intro F ρ p k B K A e hρ hp hB hA he heK
  obtain ⟨hfin, hμ0, -, hrm⟩ := hGibbs F ρ p hρ hp
  haveI := hfin
  set μ := cutoffLaw F ρ p with hμ
  have hr : IsRadialCutoff ρ (radialProfile ρ p) := hRad ρ p hρ hp
  let W : StepVariable (finiteCells F) → ℝ := slopeDominator p
  have hW1 : ∀ η, 1 ≤ W η := one_le_slopeDominator
  have hWm : Measurable W := measurable_slopeDominator
  have hnn : ∀ η : StepVariable (finiteCells F), 0 ≤ cutoffWeight ρ p η := fun η =>
    Finset.prod_nonneg fun b _ => by
      unfold cutoffFactor
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
  have hfac : ∀ (η : StepVariable (finiteCells F)) b,
      cutoffFactor ρ p ‖η b‖ = radialProfile ρ p ‖η b‖ :=
    fun η b => by simp [radialProfile, max_eq_left (norm_nonneg (η b))]
  have hrc : Continuous (radialProfile ρ p) := hr.smooth.continuous
  have hdc : Continuous (deriv (radialProfile ρ p)) := hr.smooth.continuous_deriv le_rfl
  have hG : (fun η : StepVariable (finiteCells F) => W η * cutoffWeight ρ p η) =
      fun η => (∏ b, radialProfile ρ p ‖η b‖) +
        ∑ b, |deriv (radialProfile ρ p) ‖η b‖| *
          ∏ b' ∈ Finset.univ.erase b, radialProfile ρ p ‖η b'‖ := by
    funext η
    have e1 : cutoffWeight ρ p η = ∏ b, radialProfile ρ p ‖η b‖ :=
      Finset.prod_congr rfl fun b _ => hfac η b
    show slopeDominator p η * _ = _
    unfold slopeDominator
    rw [add_mul, one_mul, e1, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← bondSlopeWeight_mul_cutoffFactor hρ hp hr (η b), hfac, mul_assoc,
      Finset.mul_prod_erase Finset.univ (fun b => radialProfile ρ p ‖η b‖) (Finset.mem_univ b)]
  have hGc : Continuous fun η : StepVariable (finiteCells F) => W η * cutoffWeight ρ p η := by
    rw [hG]
    refine (continuous_finset_prod _ fun b _ => hrc.comp (continuous_apply b).norm).add
      (continuous_finset_sum _ fun b _ => ?_)
    exact (hdc.comp (continuous_apply b).norm).abs.mul
      (continuous_finset_prod _ fun b' _ => hrc.comp (continuous_apply b').norm)
  have hK : IsCompact {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ ≤ ρ} := by
    have : {η : StepVariable (finiteCells F) | ∀ b, ‖η b‖ ≤ ρ} =
        Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
      ext η
      simp
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hcs : HasCompactSupport fun η : StepVariable (finiteCells F) => W η * cutoffWeight ρ p η :=
    HasCompactSupport.intro hK fun η hη => by
      have h1 : ¬ ∀ b, ‖η b‖ ≤ ρ := hη
      push Not at h1
      obtain ⟨b, hb⟩ := h1
      have h2 : cutoffWeight ρ p η = 0 := by
        unfold cutoffWeight
        exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mpr hb.le])
      simp [h2]
  have hGi : Integrable (fun η : StepVariable (finiteCells F) => W η * cutoffWeight ρ p η) volume :=
    hGc.integrable_of_hasCompactSupport hcs
  have hwm : Measurable fun η : StepVariable (finiteCells F) =>
      ENNReal.ofReal (cutoffWeight ρ p η) := by
    have : Continuous (cutoffWeight (F := F) ρ p) := by
      have e1 : cutoffWeight (F := F) ρ p = fun η => ∏ b, radialProfile ρ p ‖η b‖ := by
        funext η
        exact Finset.prod_congr rfl fun b _ => hfac η b
      rw [e1]
      exact continuous_finset_prod _ fun b _ => hrc.comp (continuous_apply b).norm
    exact this.measurable.ennreal_ofReal
  have hWi : Integrable W μ := by
    rw [hμ, cutoffLaw, integrable_withDensity_iff hwm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine hGi.congr (Filter.Eventually.of_forall fun η => ?_)
    simp [ENNReal.toReal_ofReal (hnn η)]
  set ν := μ.withDensity fun η => ENNReal.ofReal (W η) with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hWi.2
  have hac : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have wm : ∀ A₀ a : StepVariable (finiteCells F) → ℝ,
      gibbsMean μ A₀ a = ballExpectation (cutoffFactor ρ p) A₀ a := fun A₀ a => (hrm A₀ a).symm
  have sm : ∀ A₀ f S : StepVariable (finiteCells F) → ℝ, (∀ η, W η * f η = S η) →
      tiltedMean ν μ A₀ f = ballExpectation (cutoffFactor ρ p) A₀ S := by
    intro A₀ f S hS
    rw [← wm]
    unfold tiltedMean gibbsMean
    congr 1
    rw [hν, integral_withDensity_eq_integral_toReal_smul hWm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    have h0 : 0 ≤ W η := by linarith [hW1 η]
    simp only [ENNReal.toReal_ofReal h0, smul_eq_mul]
    rw [← hS η]
    ring
  have sc : ∀ A₀ f S g : StepVariable (finiteCells F) → ℝ, (∀ η, W η * f η = S η) →
      tiltedCov ν μ A₀ f g = ballCovariance (cutoffFactor ρ p) A₀ S g := by
    intro A₀ f S g hS
    unfold tiltedCov ballCovariance
    rw [sm A₀ (fun η => f η * g η) (fun η => S η * g η) (fun η => by rw [← hS η]; ring),
      sm A₀ f S hS, wm]
  have st : ∀ A₀ f S g h : StepVariable (finiteCells F) → ℝ, (∀ η, W η * f η = S η) →
      tiltedCumulantThree ν μ A₀ f g h = ballThirdCumulant (cutoffFactor ρ p) A₀ S g h := by
    intro A₀ f S g h hS
    unfold tiltedCumulantThree ballThirdCumulant
    rw [sm A₀ (fun η => f η * g η * h η) (fun η => S η * g η * h η)
        (fun η => by rw [← hS η]; ring),
      sm A₀ (fun η => f η * g η) (fun η => S η * g η) (fun η => by rw [← hS η]; ring),
      sm A₀ (fun η => f η * h η) (fun η => S η * h η) (fun η => by rw [← hS η]; ring),
      sm A₀ f S hS]
    simp only [wm]
  have sf : ∀ A₀ f S g h l : StepVariable (finiteCells F) → ℝ, (∀ η, W η * f η = S η) →
      tiltedCumulantFour ν μ A₀ f g h l = ballFourthCumulant (cutoffFactor ρ p) A₀ S g h l := by
    intro A₀ f S g h l hS
    unfold tiltedCumulantFour ballFourthCumulant
    rw [sm A₀ (fun η => f η * g η * h η * l η) (fun η => S η * g η * h η * l η)
        (fun η => by rw [← hS η]; ring),
      sm A₀ (fun η => f η * g η * h η) (fun η => S η * g η * h η) (fun η => by rw [← hS η]; ring),
      sm A₀ (fun η => f η * g η * l η) (fun η => S η * g η * l η) (fun η => by rw [← hS η]; ring),
      sm A₀ (fun η => f η * h η * l η) (fun η => S η * h η * l η) (fun η => by rw [← hS η]; ring),
      sm A₀ (fun η => f η * g η) (fun η => S η * g η) (fun η => by rw [← hS η]; ring),
      sm A₀ (fun η => f η * h η) (fun η => S η * h η) (fun η => by rw [← hS η]; ring),
      sm A₀ (fun η => f η * l η) (fun η => S η * l η) (fun η => by rw [← hS η]; ring),
      sm A₀ f S hS]
    simp only [wm]
  let H : (Fin k → ℝ) → StepVariable (finiteCells F) → ℝ := fun τ η => normalizedSlopeCLM p η (e τ)
  have hFD : ∀ τ ∈ B, ∀ j, j ≤ 3 → ∀ (v : Fin j → Fin k → ℝ) (η : StepVariable (finiteCells F)),
      iteratedFDeriv ℝ j (fun τ' => H τ' η) τ =
        (normalizedSlopeCLM p η).compContinuousMultilinearMap (iteratedFDeriv ℝ j e τ) := by
    intro τ hτ j hj v η
    have hat : ContDiffAt ℝ j e τ :=
      (he.contDiffAt (hB.mem_nhds hτ)).of_le (by exact_mod_cast hj)
    exact (normalizedSlopeCLM p η).iteratedFDeriv_comp_left hat (i := j) le_rfl
  have hH : IsDominatedSmoothFamily μ 3 B K H := by
    refine ⟨fun τ _ => ?_, Filter.Eventually.of_forall fun η => ?_,
      Filter.Eventually.of_forall fun η j hj τ hτ => ?_⟩
    · have h1 : H τ = fun η => (slopeDominator p η)⁻¹ * cutoffSlope p (e τ) η := by
        funext η
        simp only [H, normalizedSlopeCLM, ContinuousLinearMap.smul_apply, smul_eq_mul,
          slopeCLM_apply]
      rw [h1]
      exact (hWm.inv.mul (measurable_cutoffSlope p _)).aestronglyMeasurable
    · exact (normalizedSlopeCLM p η).contDiff.comp_contDiffOn he
    · have h1 := hFD τ hτ j hj (fun _ => 0) η
      rw [h1]
      refine ((normalizedSlopeCLM p η).norm_compContinuousMultilinearMap_le _).trans ?_
      calc ‖normalizedSlopeCLM p η‖ * ‖iteratedFDeriv ℝ j e τ‖ ≤ 1 * ‖iteratedFDeriv ℝ j e τ‖ :=
            mul_le_mul_of_nonneg_right (norm_normalizedSlopeCLM_le p η) (norm_nonneg _)
        _ ≤ K := by
            rw [one_mul]
            exact heK j hj τ hτ
  obtain ⟨c3, hform⟩ := hTilt _ ν μ k B K A H hB hμ0 hac hA hH
  have S0 : ∀ τ η, W η * H τ η = cutoffSlope p (e τ) η :=
    fun τ η => slopeDominator_mul_normalizedSlopeCLM p η (e τ)
  have eF : (fun τ => tiltedMean ν μ (A τ) (H τ)) =
      fun τ => ballExpectation (cutoffFactor ρ p) (A τ) (cutoffSlope p (e τ)) :=
    funext fun τ => sm _ _ _ (S0 τ)
  rw [eF] at c3
  refine ⟨c3, fun τ hτ u v w => ?_⟩
  obtain ⟨f1, f2, f3⟩ := hform τ hτ u v w
  rw [eF] at f1 f2 f3
  have SJ : ∀ j, j ≤ 3 → ∀ (vv : Fin j → Fin k → ℝ) (η : StepVariable (finiteCells F)),
      W η * paramIteratedDeriv H vv τ η = cutoffSlope p (iteratedFDeriv ℝ j e τ vv) η := by
    intro j hj vv η
    have h1 : paramIteratedDeriv H vv τ η =
        normalizedSlopeCLM p η (iteratedFDeriv ℝ j e τ vv) := by
      unfold paramIteratedDeriv
      rw [hFD τ hτ j hj vv η]
      rfl
    rw [h1]
    exact slopeDominator_mul_normalizedSlopeCLM p η _
  have S1 := fun u' => SJ 1 (by norm_num) ![u']
  have S2 := fun v' u' => SJ 2 (by norm_num) ![v', u']
  have S3 := SJ 3 le_rfl ![w, v, u]
  refine ⟨?_, ?_, ?_⟩
  · rw [f1, sm _ _ _ (S1 u), sc _ _ _ _ (S0 τ)]
  · rw [f2, sm _ _ _ (S2 v u), sc _ _ _ _ (S1 u), sc _ _ _ _ (S1 v), sc _ _ _ _ (S0 τ),
      st _ _ _ _ _ (S0 τ)]
  · rw [f3, sm _ _ _ S3, sc _ _ _ _ (S2 v u), sc _ _ _ _ (S2 w u), sc _ _ _ _ (S2 w v),
      sc _ _ _ _ (S1 u), sc _ _ _ _ (S1 v), sc _ _ _ _ (S1 w), st _ _ _ _ _ (S1 u),
      st _ _ _ _ _ (S1 v), st _ _ _ _ _ (S1 w), sc _ _ _ _ (S0 τ), st _ _ _ _ _ (S0 τ),
      st _ _ _ _ _ (S0 τ), st _ _ _ _ _ (S0 τ), sf _ _ _ _ _ _ (S0 τ)]
end Cumulants
end YangMills.Construction
end
