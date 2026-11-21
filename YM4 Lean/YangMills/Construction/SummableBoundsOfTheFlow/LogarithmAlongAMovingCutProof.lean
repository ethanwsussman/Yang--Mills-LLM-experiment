import YangMills.Construction.ClusterExpansionOfAStep.SecondMomentOfAConvexLawProof
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfTheMeanOfASlopeProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped RealInnerProductSpace Topology
open MeasureTheory Set Filter
namespace YangMills.Construction.Estimates
open YangMills.Construction.ColdStepAtMirrorFrames
namespace ShiftedCutoff
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def radialCutoffFactor (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : ℝ := cutoffFactor ρ p (max u 0)
theorem radialWeightProd_radialCutoffFactor (ρ : ℝ) (p : ℝ → ℝ) (η : BondField ι) :
    radialWeightProd (radialCutoffFactor ρ p) η = radialWeightProd (cutoffFactor ρ p) η := by
  unfold radialWeightProd radialCutoffFactor
  exact Finset.prod_congr rfl fun b _ => by rw [max_eq_left (norm_nonneg _)]
theorem radialCutoffFactor_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ radialCutoffFactor ρ p u := by apply _root_.YangMills.Construction.Cumulants.SlopeMeanDerivatives.radialProfile_nonneg <;> assumption
theorem contDiff_radialWeightProd {ρ : ℝ} {r : ℝ → ℝ} (hρ : 0 < ρ) (hr : IsRadialCutoff ρ r) :
    ContDiff ℝ 1 (radialWeightProd (ι := ι) r) := by apply _root_.YangMills.Construction.ConvexBallLaws.SecondMoment.contDiff_radialWeightProd <;> assumption
theorem hasDerivAt_norm_sub_smul {v e : BondVector} (hv : v ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖v - t • e‖) (-(‖v‖⁻¹ * ⟪v, e⟫)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => v - t • e) (-e) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const e).const_sub v
    simpa using this
  have h2 := h1.norm_sq
  have h3 : (‖v - (0 : ℝ) • e‖ ^ 2) ≠ 0 := by
    simpa using hv
  have h4 := h2.sqrt h3
  have e1 : (fun t : ℝ => Real.sqrt (‖v - t • e‖ ^ 2)) = fun t : ℝ => ‖v - t • e‖ := by
    funext t
    exact Real.sqrt_sq (norm_nonneg _)
  rw [e1] at h4
  convert h4 using 1
  simp only [zero_smul, sub_zero, inner_neg_right]
  rw [Real.sqrt_sq (norm_nonneg _)]
  field_simp
theorem hasDerivAt_radialCutoffFactor_norm_sub_smul {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ)
    (hp : IsCutoff ρ p) (hr : IsRadialCutoff ρ (radialCutoffFactor ρ p)) (v e : BondVector) :
    HasDerivAt (fun t : ℝ => radialCutoffFactor ρ p ‖v - t • e‖)
      (radialCutoffFactor ρ p ‖v‖ * (deriv p ‖v‖ * ‖v‖⁻¹ * ⟪v, e⟫)) 0 := by
  by_cases hv : v = 0
  · subst hv
    have hc : Tendsto (fun t : ℝ => ‖(0 : BondVector) - t • e‖) (𝓝 0) (𝓝 0) := by
      have : Continuous fun t : ℝ => ‖(0 : BondVector) - t • e‖ := by fun_prop
      simpa using this.tendsto 0
    have hev : (fun t : ℝ => radialCutoffFactor ρ p ‖(0 : BondVector) - t • e‖) =ᶠ[𝓝 0]
        fun _ => (1 : ℝ) := by
      filter_upwards [hc.eventually (gt_mem_nhds (show (0 : ℝ) < 5 * ρ / 8 by positivity))] with t ht
      exact hr.one _ (norm_nonneg _) ht.le
    have := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq hev
    simpa using this
  · have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hn := hasDerivAt_norm_sub_smul (e := e) hv
    have hd : HasDerivAt (radialCutoffFactor ρ p) (deriv (radialCutoffFactor ρ p) ‖v‖) ‖v‖ :=
      (hr.smooth.differentiable (by norm_num) _).hasDerivAt
    have hn' : HasDerivAt (fun t : ℝ => ‖v - t • e‖) (-(‖v‖⁻¹ * ⟪v, e⟫)) 0 := hn
    have hcomp : HasDerivAt (fun t : ℝ => radialCutoffFactor ρ p ‖v - t • e‖)
        (deriv (radialCutoffFactor ρ p) ‖v‖ * (-(‖v‖⁻¹ * ⟪v, e⟫))) 0 := by
      have hd0 : HasDerivAt (radialCutoffFactor ρ p) (deriv (radialCutoffFactor ρ p) ‖v‖)
          ‖v - (0 : ℝ) • e‖ := by simpa using hd
      exact HasDerivAt.comp (h₂ := radialCutoffFactor ρ p) (h := fun t : ℝ => ‖v - t • e‖)
        (0 : ℝ) hd0 hn'
    convert hcomp using 1
    by_cases hu : ‖v‖ < ρ
    · have hpd : HasDerivAt p (deriv p ‖v‖) ‖v‖ := by
        have hs : Ico 0 ρ ∈ 𝓝 ‖v‖ := Ico_mem_nhds hpos hu
        have := ((hp.smooth.contDiffAt hs).differentiableAt (by simp)).hasDerivAt
        exact this
      have hev : radialCutoffFactor ρ p =ᶠ[𝓝 ‖v‖] fun u => Real.exp (- p u) := by
        filter_upwards [Ioo_mem_nhds hpos hu] with u hu'
        unfold radialCutoffFactor cutoffFactor
        rw [max_eq_left hu'.1.le, if_pos hu'.2]
      have hexp : HasDerivAt (fun u => Real.exp (- p u))
          (Real.exp (- p ‖v‖) * (- deriv p ‖v‖)) ‖v‖ :=
        hpd.neg.exp
      have hexp' : deriv (radialCutoffFactor ρ p) ‖v‖ = Real.exp (- p ‖v‖) * (- deriv p ‖v‖) :=
        (hexp.congr_of_eventuallyEq hev).deriv
      have hval : radialCutoffFactor ρ p ‖v‖ = Real.exp (- p ‖v‖) := by
        unfold radialCutoffFactor cutoffFactor
        rw [max_eq_left hpos.le, if_pos hu]
      rw [hexp', hval]
      ring
    · have hz : radialCutoffFactor ρ p ‖v‖ = 0 := hr.zero _ (not_lt.mp hu)
      have hm : IsLocalMin (radialCutoffFactor ρ p) ‖v‖ :=
        Eventually.of_forall fun u => by rw [hz]; exact radialCutoffFactor_nonneg ρ p u
      rw [hm.deriv_eq_zero, hz]
      ring
theorem neg_fderiv_radialWeightProd {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p)
    (hr : IsRadialCutoff ρ (radialCutoffFactor ρ p)) (η e : BondField ι) :
    -(fderiv ℝ (radialWeightProd (ι := ι) (radialCutoffFactor ρ p)) η e) =
      cutoffSlope p e η * radialWeightProd (radialCutoffFactor ρ p) η := by
  have hdiff : DifferentiableAt ℝ (radialWeightProd (ι := ι) (radialCutoffFactor ρ p)) η :=
    ((contDiff_radialWeightProd hρ hr).differentiable (by norm_num)) η
  have hline : HasDerivAt (fun t : ℝ => η - t • e) (-e) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const e).const_sub η
    simpa using this
  have h1 : HasDerivAt (fun t : ℝ => radialWeightProd (radialCutoffFactor ρ p) (η - t • e))
      (fderiv ℝ (radialWeightProd (ι := ι) (radialCutoffFactor ρ p)) η (-e)) 0 := by
    have hd : HasFDerivAt (radialWeightProd (ι := ι) (radialCutoffFactor ρ p))
        (fderiv ℝ (radialWeightProd (ι := ι) (radialCutoffFactor ρ p)) η) (η - (0 : ℝ) • e) := by
      simpa using hdiff.hasFDerivAt
    exact hd.comp_hasDerivAt (0 : ℝ) hline
  have h2 : HasDerivAt (fun t : ℝ => radialWeightProd (radialCutoffFactor ρ p) (η - t • e))
      (∑ b, (∏ b' ∈ Finset.univ.erase b, radialCutoffFactor ρ p ‖η b'‖) •
        (radialCutoffFactor ρ p ‖η b‖ * (deriv p ‖η b‖ * ‖η b‖⁻¹ * ⟪η b, e b⟫))) 0 := by
    have := HasDerivAt.fun_finsetProd (u := Finset.univ) (x := (0 : ℝ))
      (f := fun (b : ι) (t : ℝ) => radialCutoffFactor ρ p ‖(η - t • e) b‖)
      (f' := fun b => radialCutoffFactor ρ p ‖η b‖ * (deriv p ‖η b‖ * ‖η b‖⁻¹ * ⟪η b, e b⟫))
      (fun b _ => by simpa using hasDerivAt_radialCutoffFactor_norm_sub_smul hρ hp hr (η b) (e b))
    simpa [radialWeightProd] using this
  have h3 := h1.unique h2
  rw [map_neg] at h3
  rw [h3]
  unfold cutoffSlope radialWeightProd
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_eq_mul,
    ← Finset.prod_erase_mul Finset.univ (fun b => radialCutoffFactor ρ p ‖η b‖) (Finset.mem_univ b)]
  ring
theorem measurable_cutoffSlope (p : ℝ → ℝ) (e : BondField ι) :
    Measurable (cutoffSlope (ι := ι) p e) := by apply _root_.YangMills.Construction.Cumulants.SlopeMeanDerivatives.measurable_cutoffSlope <;> assumption
theorem exists_abs_le_of_vanish_off_balls {ρ : ℝ} (hρ : 0 < ρ) {Φ : BondField ι → ℝ}
    (hc : Continuous Φ) (h0 : ∀ η, ¬ (∀ b, ‖η b‖ < ρ) → Φ η = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ η, |Φ η| ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : BondField ι) ρ).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun η => ?_⟩
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · have : η ∈ Metric.closedBall (0 : BondField ι) ρ := by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hρ.le]
      exact fun b => (hη b).le
    exact (hC η this).trans (le_max_left _ _)
  · rw [h0 η hη, abs_zero]
    exact le_max_right _ _
end ShiftedCutoff
open ShiftedCutoff in
theorem logShiftedCutoffIntegral_of_cutoffFactor (hrad : CutoffFactorIsRadialCutoff) :
    logShiftedCutoffIntegralStatement := by
  classical
  intro ι _ _ ρ p G a d M hρ hp hmeas hG hZ
  have hr : IsRadialCutoff ρ (radialCutoffFactor ρ p) := hrad ρ p hρ hp
  set K : BondField ι → ℝ := radialWeightProd (ι := ι) (radialCutoffFactor ρ p) with hKdef
  have hKe : ∀ η, radialWeightProd (cutoffFactor ρ p) η = K η := fun η =>
    (radialWeightProd_radialCutoffFactor ρ p η).symm
  have hKc : ContDiff ℝ 1 K := contDiff_radialWeightProd hρ hr
  let Q : BondField ι → BondField ι → ℝ := fun e η => -(fderiv ℝ K η e)
  have hQ : ∀ e η, cutoffSlope p e η * K η = Q e η := fun e η =>
    (neg_fderiv_radialWeightProd hρ hp hr η e).symm
  have hQc : ∀ e, Continuous (Q e) := fun e =>
    ((hKc.continuous_fderiv (by norm_num)).clm_apply continuous_const).neg
  have hK0 : ∀ η, ¬ (∀ b, ‖η b‖ < ρ) → K η = 0 := by
    intro η hη
    push Not at hη
    obtain ⟨b, hb⟩ := hη
    exact Finset.prod_eq_zero (Finset.mem_univ b) (hr.zero _ hb)
  have hQ0 : ∀ e η, ¬ (∀ b, ‖η b‖ < ρ) → Q e η = 0 := by
    intro e η hη
    rw [← hQ, hK0 η hη, mul_zero]
  let sh : ℝ → BondField ι → BondField ι := fun s w => w - (a + s • d)
  have hshc : ∀ w, Continuous fun s => sh s w := fun w => by
    show Continuous fun s : ℝ => w - (a + s • d)
    fun_prop
  have hshm : ∀ s, Measurable (sh s) := fun s => by
    show Measurable fun w : BondField ι => w - (a + s • d)
    exact measurable_id.sub_const _
  have hdom : ∀ Φ : BondField ι → ℝ, Continuous Φ → (∀ η, ¬ (∀ b, ‖η b‖ < ρ) → Φ η = 0) →
      ∃ bound : BondField ι → ℝ, Integrable bound ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ w, ‖G w * Φ (sh s w)‖ ≤ bound w := by
    intro Φ hc h0
    obtain ⟨B, hB0, hB⟩ := exists_abs_le_of_vanish_off_balls hρ hc h0
    set R : ℝ := ρ + ‖a‖ + ‖d‖ with hR
    refine ⟨(Metric.closedBall (0 : BondField ι) R).indicator fun _ => |M| * B, ?_, ?_⟩
    · exact (integrableOn_const (measure_closedBall_lt_top).ne).integrable_indicator
        Metric.isClosed_closedBall.measurableSet
    · intro s hs w
      by_cases hη : ∀ b, ‖(sh s w) b‖ < ρ
      · have hin : w ∈ Metric.closedBall (0 : BondField ι) R := by
          rw [mem_closedBall_zero_iff]
          have h1 : ‖sh s w‖ ≤ ρ := (pi_norm_le_iff_of_nonneg hρ.le).mpr fun b => (hη b).le
          have h2 : w = sh s w + (a + s • d) := by
            show w = w - (a + s • d) + (a + s • d)
            abel
          have h3 : ‖s • d‖ ≤ ‖d‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
            exact mul_le_of_le_one_left (norm_nonneg _) hs.2
          calc ‖w‖ = ‖sh s w + (a + s • d)‖ := by rw [← h2]
            _ ≤ ‖sh s w‖ + (‖a‖ + ‖s • d‖) := (norm_add_le _ _).trans
                (add_le_add_right (norm_add_le _ _) _)
            _ ≤ R := by rw [hR]; linarith
        rw [indicator_of_mem hin, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul ((hG s hs w hη).trans (le_abs_self M)) (hB _) (abs_nonneg _) (abs_nonneg _)
      · rw [h0 _ hη, mul_zero, norm_zero]
        exact indicator_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) hB0) _
  have hmK : ∀ s ∈ Icc (0 : ℝ) 1, AEStronglyMeasurable (fun w => G w * K (sh s w)) volume := by
    intro s hs
    have := hmeas s hs
    simp only [hKe] at this
    exact this
  have hmQ : ∀ e, ∀ s ∈ Icc (0 : ℝ) 1,
      AEStronglyMeasurable (fun w => G w * Q e (sh s w)) volume := by
    intro e s hs
    have hE : (fun w => G w * Q e (sh s w)) =
        fun w => (G w * K (sh s w)) * cutoffSlope p e (sh s w) := by
      funext w
      rw [← hQ]
      ring
    rw [hE]
    exact (hmK s hs).mul ((measurable_cutoffSlope p e).comp (hshm s)).aestronglyMeasurable
  have hcont : ∀ Φ : BondField ι → ℝ, Continuous Φ → (∀ η, ¬ (∀ b, ‖η b‖ < ρ) → Φ η = 0) →
      (∀ s ∈ Icc (0 : ℝ) 1, AEStronglyMeasurable (fun w => G w * Φ (sh s w)) volume) →
      ContinuousOn (fun s => ∫ w, G w * Φ (sh s w)) (Icc (0 : ℝ) 1) := by
    intro Φ hc h0 hm s₀ _
    obtain ⟨bound, hbi, hb⟩ := hdom Φ hc h0
    refine continuousWithinAt_of_dominated (bound := bound) ?_ ?_ hbi ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs using hm s hs
    · filter_upwards [self_mem_nhdsWithin] with s hs using Eventually.of_forall (hb s hs)
    · exact Eventually.of_forall fun w =>
        (continuous_const.mul (hc.comp (hshc w))).continuousWithinAt
  have hKc0 : Continuous K := hKc.continuous
  have hZc := hcont K hKc0 hK0 hmK
  have hSc : ∀ e, ContinuousOn (fun s => ∫ w, G w * Q e (sh s w)) (Icc (0 : ℝ) 1) := fun e =>
    hcont (Q e) (hQc e) (hQ0 e) (hmQ e)
  have eZ : ∀ s, shiftedCutoffIntegral ρ p G a d s = ∫ w, G w * K (sh s w) := by
    intro s
    unfold shiftedCutoffIntegral
    simp only [hKe]
    rfl
  have eS : ∀ e s, shiftedCutoffSlopeIntegral ρ p G a d e s = ∫ w, G w * Q e (sh s w) := by
    intro e s
    unfold shiftedCutoffSlopeIntegral
    simp only [hKe, hQ]
    rfl
  have hZ' : ∀ s ∈ Icc (0 : ℝ) 1, 0 < ∫ w, G w * K (sh s w) := fun s hs => by
    rw [← eZ]
    exact hZ s hs
  have hder : ∀ s ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun s => ∫ w, G w * K (sh s w)) (∫ w, G w * Q d (sh s w)) s := by
    intro s hs
    obtain ⟨bound, hbi, hb⟩ := hdom (Q d) (hQc d) (hQ0 d)
    obtain ⟨boundK, hbKi, hbK⟩ := hdom K hKc0 hK0
    have hsS : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := bound)
      (F := fun s w => G w * K (sh s w)) (F' := fun s w => G w * Q d (sh s w))
      (Ioo_mem_nhds hs.1 hs.2) ?_ ?_ (hmQ d s hsS) ?_ hbi ?_).2
    · filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs' using hmK s' (Ioo_subset_Icc_self hs')
    · exact hbKi.mono' (hmK s hsS) (Eventually.of_forall (hbK s hsS))
    · exact Eventually.of_forall fun w s' hs' => hb s' (Ioo_subset_Icc_self hs') w
    · refine Eventually.of_forall fun w s' _ => ?_
      have hline : HasDerivAt (fun s => sh s w) (-d) s' := by
        have := (((hasDerivAt_id s').smul_const d).const_add a).const_sub w
        simpa using this
      have hf : HasFDerivAt K (fderiv ℝ K (sh s' w)) (sh s' w) :=
        ((hKc.differentiable (by norm_num)) _).hasFDerivAt
      have := (hf.comp_hasDerivAt s' hline).const_mul (G w)
      simpa [Q, map_neg] using this
  refine ⟨?_, ?_, ?_⟩
  · intro e s hs
    obtain ⟨bound, hbi, hb⟩ := hdom (Q e) (hQc e) (hQ0 e)
    have hi := hbi.mono' (hmQ e s hs) (Eventually.of_forall (hb s hs))
    simpa only [hKe, hQ] using hi
  · intro e
    have h1 : (fun s => shiftedCutoffSlopeIntegral ρ p G a d e s / shiftedCutoffIntegral ρ p G a d s) =
        fun s => (∫ w, G w * Q e (sh s w)) / ∫ w, G w * K (sh s w) := by
      funext s
      rw [eS, eZ]
    rw [h1]
    exact (hSc e).div hZc fun s hs => (hZ' s hs).ne'
  · have h1 : (fun s => shiftedCutoffSlopeIntegral ρ p G a d d s / shiftedCutoffIntegral ρ p G a d s) =
        fun s => (∫ w, G w * Q d (sh s w)) / ∫ w, G w * K (sh s w) := by
      funext s
      rw [eS, eZ]
    have hq : ContinuousOn (fun s => (∫ w, G w * Q d (sh s w)) / ∫ w, G w * K (sh s w))
        (Icc (0 : ℝ) 1) := (hSc d).div hZc fun s hs => (hZ' s hs).ne'
    have hint : IntervalIntegrable (fun s => (∫ w, G w * Q d (sh s w)) / ∫ w, G w * K (sh s w))
        volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rwa [uIcc_of_le zero_le_one]
    have hlogc : ContinuousOn (fun s => Real.log (∫ w, G w * K (sh s w))) (Icc (0 : ℝ) 1) :=
      hZc.log fun s hs => (hZ' s hs).ne'
    have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hlogc
      (fun s hs => ((hder s hs).log (hZ' s (Ioo_subset_Icc_self hs)).ne').hasDerivWithinAt) hint
    rw [h1, eZ, eZ]
    exact hftc.symm
end YangMills.Construction.Estimates
end
