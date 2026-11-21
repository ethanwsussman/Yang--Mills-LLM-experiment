import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.LawByMomentsOfTheFlow.ColdDensityOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.ColdFineField
import YangMills.Construction.LawByMomentsOfTheFlow.CompletedFormAcrossAStepProof
import YangMills.Construction.LawByMomentsOfTheFlow.ContractionOfTheResponse
import YangMills.Construction.LawByMomentsOfTheFlow.GoodStateForgets
import YangMills.Construction.LawByMomentsOfTheFlow.MeanAtTheCutOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.MeanOverTheFluctuationOfAGoodState
import YangMills.Construction.LawByMomentsOfTheFlow.MeansOfFormsAtAWeight
import YangMills.Construction.LawByMomentsOfTheFlow.OneStepOfTheMeansOfForms
import YangMills.Construction.LawByMomentsOfTheFlow.TheCutOfAGoodState
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction
open MomentLaw TorusFields TorusLumps StepSettings WeightedResponses TorusContours
namespace MomentLaw
namespace FormProductStep
section Density
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem chartDensity_nonneg (s : ChartSetting R n) (η : FreeCoords s.free) : 0 ≤ chartDensity s η := by apply _root_.YangMills.Construction.ResponseInTheExpansion.FarSpin.chartDensity_nonneg <;> assumption
private theorem coordNorm_lt_of_chartDensity_ne_zero (s : ChartSetting R n) (η : FreeCoords s.free)
    (h : chartDensity s η ≠ 0) (b : s.free) :
    coordNorm (η b) < R.ballRadius := by
  by_contra hb
  apply h
  unfold chartDensity ChartSetting.cutoffProduct
  rw [Finset.prod_eq_zero (Finset.mem_univ b) (by unfold ColdStepAtMirrorFrames.cutoffFactor; exact if_neg hb), zero_mul]
private theorem normalizedLaw_facts (s : ChartSetting R n) (hI : Integrable (chartDensity s))
    (hp : 0 < ∫ η, chartDensity s η) :
    IsProbabilityMeasure (((∫⁻ η, ENNReal.ofReal (chartDensity s η))⁻¹) •
      (volume.withDensity fun η => ENNReal.ofReal (chartDensity s η))) ∧
    (∀ G : FreeCoords s.free → ℝ, weightedMean (chartDensity s) G =
      ∫ η, G η ∂(((∫⁻ η, ENNReal.ofReal (chartDensity s η))⁻¹) •
        (volume.withDensity fun η => ENNReal.ofReal (chartDensity s η)))) ∧
    ∀ᵐ η ∂(((∫⁻ η, ENNReal.ofReal (chartDensity s η))⁻¹) •
      (volume.withDensity fun η => ENNReal.ofReal (chartDensity s η))), ∀ b, coordNorm (η b) < R.ballRadius := by
  have hmass : ∫⁻ η, ENNReal.ofReal (chartDensity s η) = ENNReal.ofReal (∫ η, chartDensity s η) :=
    (ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ (chartDensity_nonneg s))).symm
  have hm0 : ∫⁻ η, ENNReal.ofReal (chartDensity s η) ≠ 0 := by
    rw [hmass]
    exact (ENNReal.ofReal_pos.2 hp).ne'
  have hmT : ∫⁻ η, ENNReal.ofReal (chartDensity s η) ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.ofReal_ne_top
  have hfm : AEMeasurable (fun η => ENNReal.ofReal (chartDensity s η)) volume :=
    hI.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  refine ⟨⟨?_⟩, fun G => ?_, ?_⟩
  · rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hm0 hmT
  · rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul₀ hfm
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    unfold weightedMean
    rw [ENNReal.toReal_inv, hmass, ENNReal.toReal_ofReal hp.le, div_eq_inv_mul, smul_eq_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun η => ?_)
    simp only [ENNReal.toReal_ofReal (chartDensity_nonneg s η), smul_eq_mul]
    ring
  · rw [ae_iff, Measure.smul_apply, smul_eq_mul]
    have h0 : (volume.withDensity fun η => ENNReal.ofReal (chartDensity s η))
        {η | ¬ ∀ b, coordNorm (η b) < R.ballRadius} = 0 := by
      rw [withDensity_apply_eq_zero' hfm]
      convert measure_empty (μ := (volume : Measure (FreeCoords s.free)))
      ext η
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro h
      refine coordNorm_lt_of_chartDensity_ne_zero s η ?_
      intro h0
      apply h
      simp [h0]
    rw [h0, mul_zero]
end Density
section Forms
variable {n : ℕ}
private def curlVector (X : ColourForm n) (p : TorusPlaquette n) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun e => curl (X e) p
private theorem curlNorm_eq_norm (X : ColourForm n) (p : TorusPlaquette n) : curlNorm X p = ‖curlVector X p‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold curlNorm curlVector
  simp
private theorem curlNorm_sub_le (X Y : ColourForm n) (p : TorusPlaquette n) :
    curlNorm (fun e b => X e b - Y e b) p ≤ curlNorm X p + curlNorm Y p := by
  have e : curlVector (fun e b => X e b - Y e b) p = curlVector X p - curlVector Y p := by
    ext e
    simp only [curlVector, curl, PiLp.sub_apply]
    ring
  rw [curlNorm_eq_norm, curlNorm_eq_norm, curlNorm_eq_norm, e]
  exact norm_sub_le _ _
private theorem curlNorm_add_le (X Y : ColourForm n) (p : TorusPlaquette n) :
    curlNorm (fun e b => X e b + Y e b) p ≤ curlNorm X p + curlNorm Y p := by
  have e : curlVector (fun e b => X e b + Y e b) p = curlVector X p + curlVector Y p := by
    ext e
    simp only [curlVector, curl, PiLp.add_apply]
    ring
  rw [curlNorm_eq_norm, curlNorm_eq_norm, curlNorm_eq_norm, e]
  exact norm_add_le _ _
private theorem curlNorm_le_of_abs_le (X : ColourForm n) (a : ℝ) (ha : 0 ≤ a) (h : ∀ e b, |X e b| ≤ a)
    (p : TorusPlaquette n) :
    curlNorm X p ≤ 8 * a := by
  unfold curlNorm
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h1 : ∀ e : Fin 3, curl (X e) p ^ 2 ≤ (4 * a) ^ 2 := by
    intro e
    refine sq_le_sq' ?_ ?_ <;> unfold curl
    · have h₁ := abs_le.1 (h e (p.1, p.2.1))
      have h₂ := abs_le.1 (h e (p.1 + unitStep n p.2.1, p.2.2))
      have h₃ := abs_le.1 (h e (p.1 + unitStep n p.2.2, p.2.1))
      have h₄ := abs_le.1 (h e (p.1, p.2.2))
      linarith [h₁.1, h₂.1, h₃.2, h₄.2]
    · have h₁ := abs_le.1 (h e (p.1, p.2.1))
      have h₂ := abs_le.1 (h e (p.1 + unitStep n p.2.1, p.2.2))
      have h₃ := abs_le.1 (h e (p.1 + unitStep n p.2.2, p.2.1))
      have h₄ := abs_le.1 (h e (p.1, p.2.2))
      linarith [h₁.2, h₂.2, h₃.1, h₄.1]
  calc ∑ e : Fin 3, curl (X e) p ^ 2 ≤ ∑ _e : Fin 3, (4 * a) ^ 2 := Finset.sum_le_sum fun e _ => h1 e
    _ = 3 * (4 * a) ^ 2 := by simp
    _ ≤ (8 * a) ^ 2 := by nlinarith [sq_nonneg a]
private theorem abs_coord_le_coordNorm (v : EuclideanSpace ℝ (Fin 3)) (e : Fin 3) : |v e| ≤ coordNorm v := by
  have h : (v e) ^ 2 ≤ coordNorm v ^ 2 := by
    unfold coordNorm
    rw [sq ‖_‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
    simp only [ColdStepAtMirrorFrames.toImaginary]
    fin_cases e <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  exact abs_le_of_sq_le_sq h (norm_nonneg _)
end Forms
section Means
private theorem abs_integral_sub_le_of_near {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) (G₁ G₂ D : Ω → ℝ) (hG₁ : Measurable G₁) (hG₂ : Measurable G₂) (M Mg T e : ℝ)
    (hM : ∀ η, |G₁ η| ≤ M) (hMg : ∀ᵐ η ∂μ, |G₂ η| ≤ Mg) (hMg0 : 0 ≤ Mg)
    (hpoint : ∀ᵐ η ∂μ, |G₁ η - G₂ η| ≤ D η + Eᶜ.indicator (fun _ => Mg) η)
    (hT : ∫⁻ η, ENNReal.ofReal (D η) ∂μ ≤ ENNReal.ofReal T) (hT0 : 0 ≤ T)
    (hEc : μ Eᶜ ≤ ENNReal.ofReal e) (he0 : 0 ≤ e) :
    |∫ η, G₁ η ∂μ - ∫ η, G₂ η ∂μ| ≤ T + Mg * e := by
  have i₁ : Integrable G₁ μ := Integrable.of_bound hG₁.aestronglyMeasurable M (ae_of_all _ fun η => by simpa using hM η)
  have i₂ : Integrable G₂ μ := Integrable.of_bound hG₂.aestronglyMeasurable Mg (by simpa using hMg)
  have i₃ : Integrable (fun η => |G₁ η - G₂ η|) μ := (i₁.sub i₂).abs
  have h1 : |∫ η, G₁ η ∂μ - ∫ η, G₂ η ∂μ| ≤ ∫ η, |G₁ η - G₂ η| ∂μ := by
    rw [← integral_sub i₁ i₂]
    exact abs_integral_le_integral_abs
  refine h1.trans ?_
  have h2 : ENNReal.ofReal (∫ η, |G₁ η - G₂ η| ∂μ) = ∫⁻ η, ENNReal.ofReal |G₁ η - G₂ η| ∂μ :=
    ofReal_integral_eq_lintegral_ofReal i₃ (ae_of_all _ fun _ => abs_nonneg _)
  have h3 : ∫⁻ η, ENNReal.ofReal |G₁ η - G₂ η| ∂μ ≤
      ∫⁻ η, (ENNReal.ofReal (D η) + Eᶜ.indicator (fun _ => ENNReal.ofReal Mg) η) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hpoint] with η hη
    refine (ENNReal.ofReal_le_ofReal hη).trans ?_
    by_cases hm : η ∈ E
    · simp [hm]
    · simp only [Set.indicator_of_mem (Set.mem_compl hm)]
      exact ENNReal.ofReal_add_le
  have h4 : ∫⁻ η, (ENNReal.ofReal (D η) + Eᶜ.indicator (fun _ => ENNReal.ofReal Mg) η) ∂μ ≤
      ENNReal.ofReal (T + Mg * e) := by
    rw [lintegral_add_right _ (measurable_const.indicator hE.compl), lintegral_indicator hE.compl,
      setLIntegral_const, ENNReal.ofReal_add hT0 (mul_nonneg hMg0 he0), ENNReal.ofReal_mul hMg0]
    exact add_le_add hT (mul_le_mul_right hEc _)
  have h5 := (h2 ▸ h3).trans h4
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hT0 (mul_nonneg hMg0 he0))).1 h5
end Means
section Parameters
private theorem forAllParameters_and {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h₂ : ForAllParameters Q₂) :
    ForAllParameters fun Λ => Q₁ Λ ∧ Q₂ Λ := by apply _root_.YangMills.SharedProofs.p2495 <;> assumption
private theorem forAllParameters_mono {Q₁ Q₂ : MomentParameters → Prop} (h₁ : ForAllParameters Q₁)
    (h : ∀ Λ, Q₁ Λ → Q₂ Λ) :
    ForAllParameters Q₂ := by apply _root_.YangMills.SharedProofs.p9549 <;> assumption
private theorem forAllParameters_rate_pos_side :
    ForAllParameters fun Λ => 0 < Λ.stepParams.weightRate ∧ 64 ≤ Λ.stepParams.side := by
  intro a _
  refine ⟨64, fun _ => 1, 0, fun _ => one_pos, ?_⟩
  intro L _ hL Tb _ hTL hD _ _ _ _ _ _
  refine ⟨0, fun y _ _ _ g _ _ k _ _ _ R d _ => ⟨?_, ?_⟩⟩
  · have h := hD.rt_pos
    show 0 < (Tb.stepParameters y).rt / 2 ^ 10
    have e : (Tb.stepParameters y).rt = Tb.rt := rfl
    rw [e]
    positivity
  · show 64 ≤ (Tb.stepParameters y).side
    have e : (Tb.stepParameters y).side = Tb.side := rfl
    rw [e, hTL]
    exact hL
private theorem forAllParameters_contraction (h : responseContractionStatement) :
    ForAllParameters fun Λ => ∃ θ : ℝ, 0 ≤ θ ∧ ∀ (u n : ℕ) [NeZero n], 64 ≤ n → ∀ (X : ColourForm n) (K : ℝ),
      0 ≤ K → (∀ p : OrientedPlaquette n, curlNorm X p.1 ≤ K) →
      ∀ p : OrientedPlaquette (n * Λ.stepParams.side),
        curlNorm (pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side u X) p.1 ≤ θ * K := by
  intro a ha
  obtain ⟨Cw, hCw, L₀, rt₀, C₀, hrt, H⟩ := h a ha
  refine ⟨L₀, rt₀, C₀, hrt, ?_⟩
  intro L hL hLL Tb e1 e2 hD hS hC hrtb hC₀ Kr hKr
  obtain ⟨-, y₀, Y⟩ := H L hL hLL Tb e1 e2 hD hS hC hrtb hC₀
  refine ⟨y₀, fun y hy hr hw g _ _ k _ _ _ R d _ => ?_⟩
  refine ⟨Cw * (L : ℝ) ^ (-(1 / 2) : ℝ), by positivity, fun u n _ hn X K hK0 hK p => ?_⟩
  have hc : 0 ≤ (Tb.stepParameters y).weightRate / 8 := by
    have h1 := hD.rt_pos
    have e : (Tb.stepParameters y).weightRate = Tb.rt / 2 ^ 10 := rfl
    rw [e]
    positivity
  have hslow : IsSlowlyVaryingPair (n := n) (Tb.stepParameters y).side ((Tb.stepParameters y).weightRate / 8)
      (fun _ => 1) (fun _ => 1) := by
    intro p p'
    have : 0 ≤ (Tb.stepParameters y).weightRate / 8 *
        (1 + (TorusFields.supDist (parentBlock (Tb.stepParameters y).side p.1) p'.1 : ℝ)) := by positivity
    simpa using Real.one_le_exp this
  have h1 := Y y hy hr hw u n hn (fun _ => 1) (fun _ => 1) (fun _ => one_pos) (fun _ => one_pos) hslow Unit
    (Measure.dirac ()) (fun _ => X) 1 le_rfl (measurable_of_countable _)
  have hone : ∀ {m : ℕ} (Z : ColourForm m) (p : OrientedPlaquette m), ENNReal.ofReal (1 : ℝ) *
      eLpNorm (fun _ : Unit => curlNorm Z p.1) 1 (Measure.dirac ()) = ENNReal.ofReal (curlNorm Z p.1) := by
    intro m Z p
    rw [eLpNorm_const _ one_ne_zero (NeZero.ne _), measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (show 0 ≤ curlNorm Z p.1 from Real.sqrt_nonneg _), ENNReal.ofReal_one, one_mul]
  have h2 : weightedCurvatureNorm (Measure.dirac ()) (fun _ => 1) 1 (fun _ : Unit => X) ≤ ENNReal.ofReal K :=
    iSup_le fun p => by
      refine le_trans (le_of_eq (hone X p)) (ENNReal.ofReal_le_ofReal (hK p))
  have h3 : ENNReal.ofReal (curlNorm (pushColours (Tb.stepParameters y).coupling Tb.ρA
      (Tb.stepParameters y).side u X) p.1) ≤
      ENNReal.ofReal (Cw * (L : ℝ) ^ (-(1 / 2) : ℝ) * K) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    refine le_trans ?_ (h1.trans (mul_le_mul_right h2 _))
    refine le_trans (le_of_eq (hone _ p).symm) ?_
    exact le_iSup (fun p : OrientedPlaquette (n * (Tb.stepParameters y).side) => ENNReal.ofReal (1 : ℝ) *
      eLpNorm (fun _ : Unit => curlNorm (pushColours Tb.coupling Tb.ρA (Tb.stepParameters y).side u X) p.1) 1
        (Measure.dirac ())) p
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
end Parameters
section Estimates
private theorem exp_neg_le_factorial_div (t : ℝ) (ht : 0 < t) (N : ℕ) :
    Real.exp (-t) ≤ (N.factorial : ℝ) / t ^ N := by
  have h := Real.pow_div_factorial_le_exp t ht.le N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hp : 0 < t ^ N := by positivity
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) hp, one_mul]
  rw [div_le_iff₀ hf] at h
  linarith
private theorem exp_mul_sq_le (c δ ρ : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) :
    Real.exp (-(c * max 0 (δ - ρ))) * (1 + δ) ^ 2 ≤ 2 * (1 + ρ) ^ 2 + 4 / c ^ 2 := by
  have hc2 : 0 < 4 / c ^ 2 := by positivity
  rcases le_total δ ρ with h | h
  · rw [max_eq_left (by linarith)]
    simp only [mul_zero, neg_zero, Real.exp_zero, one_mul]
    have : (1 + δ) ^ 2 ≤ (1 + ρ) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith [sq_nonneg (1 + ρ)]
  · rw [max_eq_right (by linarith)]
    set e := δ - ρ with he
    have he0 : 0 ≤ e := by linarith
    have h1 : (1 + δ) ^ 2 ≤ 2 * (1 + ρ) ^ 2 + 2 * e ^ 2 := by
      have : δ = ρ + e := by rw [he]; ring
      rw [this]
      nlinarith [sq_nonneg (1 + ρ - e)]
    have hE : 0 < Real.exp (c * e) := Real.exp_pos _
    have h2 : (c * e) ^ 2 / 2 ≤ Real.exp (c * e) := by
      have := Real.quadratic_le_exp_of_nonneg (mul_nonneg hc.le he0)
      nlinarith [mul_nonneg hc.le he0]
    have h3 : Real.exp (-(c * e)) * (2 * e ^ 2) ≤ 4 / c ^ 2 := by
      rw [Real.exp_neg, inv_mul_eq_div, div_le_div_iff₀ hE (by positivity)]
      nlinarith
    have h4 : Real.exp (-(c * e)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hc.le he0])
    have h5 : 0 ≤ Real.exp (-(c * e)) := (Real.exp_pos _).le
    calc Real.exp (-(c * e)) * (1 + δ) ^ 2 ≤ Real.exp (-(c * e)) * (2 * (1 + ρ) ^ 2 + 2 * e ^ 2) :=
          mul_le_mul_of_nonneg_left h1 h5
      _ = Real.exp (-(c * e)) * (2 * (1 + ρ) ^ 2) + Real.exp (-(c * e)) * (2 * e ^ 2) := by ring
      _ ≤ 1 * (2 * (1 + ρ) ^ 2) + 4 / c ^ 2 := by
          refine add_le_add (mul_le_mul_of_nonneg_right h4 (by positivity)) h3
      _ = _ := by ring
end Estimates
section Coordinates
variable {n : ℕ} [NeZero n]
omit [NeZero n] in
private theorem measurable_freeCoordForm {R : StepSetup} (s : ChartSetting R n) :
    Measurable fun η : FreeCoords s.free => freeCoordForm s η := by
  classical
  refine measurable_pi_iff.2 fun e => measurable_pi_iff.2 fun b => ?_
  unfold freeCoordForm
  by_cases hb : b ∈ s.free
  · simp only [dif_pos hb]
    exact (EuclideanSpace.proj (𝕜 := ℝ) e).continuous.measurable.comp (measurable_pi_apply _)
  · simp only [dif_neg hb]
    exact measurable_const
omit [NeZero n] in
private theorem abs_freeCoordForm_le {R : StepSetup} (s : ChartSetting R n) (η : FreeCoords s.free)
    (hb : ∀ b, coordNorm (η b) < R.ballRadius) (e : Fin 3) (c : TorusBond (n * R.params.side)) :
    |freeCoordForm s η e c| ≤ |R.ballRadius| := by
  classical
  unfold freeCoordForm
  split_ifs with h
  · exact (abs_coord_le_coordNorm _ e).trans ((hb _).le.trans (le_abs_self _))
  · simp
omit [NeZero n] in
private theorem cutoffProfile_eq_one (o z : TorusSite n) (m : ℕ) (hm : 2 ≤ m) (h : TorusFields.supDist z o ≤ m) :
    cutoffProfile o m z = 1 := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : (TorusFields.supDist z o : ℝ) ≤ m := by exact_mod_cast h
  have h1 : 1 ≤ (2 * (m : ℝ) - 1 - (TorusFields.supDist z o : ℝ)) / ((m : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  unfold cutoffProfile
  rw [min_eq_left h1]
  exact max_eq_right zero_le_one
private theorem supDist_add_unitStep_le (z o : TorusSite n) (i : Fin 4) :
    TorusFields.supDist (z + unitStep n i) o ≤ TorusFields.supDist z o + 1 := by apply _root_.YangMills.SharedProofs.p13239 <;> assumption
private theorem curlNorm_cutoffCoords_sub (ℓ : StepParameters) (W : TorusField n) (o : TorusSite n) (m : ℕ)
    (hm : 2 ≤ m) (Z : ColourForm n) (p : TorusPlaquette n) (hp : TorusFields.supDist p.1 o + 1 ≤ m) :
    curlNorm (fun e b => toColourForm (cutoffCoords ℓ W o m) e b - Z e b) p =
      curlNorm (fun e b => toColourForm (axialCoords ℓ W o) e b - Z e b) p := by
  have h : ∀ b : TorusBond n, TorusFields.supDist b.1 o ≤ m → ∀ e,
      toColourForm (cutoffCoords ℓ W o m) e b = toColourForm (axialCoords ℓ W o) e b := by
    intro b hb e
    simp only [toColourForm, cutoffCoords, cutoffProfile_eq_one o b.1 m hm hb, one_smul]
  have h1 := supDist_add_unitStep_le p.1 o p.2.1
  have h2 := supDist_add_unitStep_le p.1 o p.2.2
  unfold curlNorm curl
  refine congrArg Real.sqrt (Finset.sum_congr rfl fun e _ => ?_)
  dsimp only
  rw [h (p.1, p.2.1) (by simp only; omega) e, h (p.1 + unitStep n p.2.1, p.2.2) (by simp only; omega) e,
    h (p.1 + unitStep n p.2.2, p.2.1) (by simp only; omega) e, h (p.1, p.2.2) (by simp only; omega) e]
end Coordinates
section Bounds
private theorem forget_bound (x : ℝ) (hx : 1 ≤ x) (k b : ℕ) (hb : b ≤ k) (a r₄ : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r₄) :
    a * r₄ * (1 + x ^ ((1 : ℝ) / 4)) ^ (2 * b) * Real.exp (-(x ^ ((1 : ℝ) / 200))) ≤
      a * 4 ^ k * ((200 * (k + 1)).factorial : ℝ) * r₄ * x⁻¹ := by
  have hx0 : 0 < x := by linarith
  set s := x ^ ((1 : ℝ) / 4) with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow hx (by norm_num)
  have hs2 : s ^ 2 ≤ x := by
    have e : s ^ 2 = x ^ ((1 : ℝ) / 2) := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    rw [e]
    calc x ^ ((1 : ℝ) / 2) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = x := Real.rpow_one x
  have h1 : (1 + s) ^ (2 * b) ≤ (4 * x) ^ k := by
    rw [pow_mul]
    have h2 : (1 + s) ^ 2 ≤ 4 * x := by nlinarith
    calc ((1 + s) ^ 2) ^ b ≤ (4 * x) ^ b := pow_le_pow_left₀ (by positivity) h2 b
      _ ≤ (4 * x) ^ k := pow_le_pow_right₀ (by linarith) hb
  set t := x ^ ((1 : ℝ) / 200) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hx0 _
  have h3 := exp_neg_le_factorial_div t ht0 (200 * (k + 1))
  have h4 : t ^ (200 * (k + 1)) = x ^ (k + 1) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [h4] at h3
  calc a * r₄ * (1 + s) ^ (2 * b) * Real.exp (-t)
      ≤ a * r₄ * (4 * x) ^ k * (((200 * (k + 1)).factorial : ℝ) / x ^ (k + 1)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h3 (Real.exp_pos _).le (by positivity)
    _ = _ := by
        rw [mul_pow, pow_succ]
        field_simp
private theorem rare_bound (x : ℝ) (hx : 1 ≤ x) (k b : ℕ) (hb : b ≤ k) (a r₄ K Cn : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r₄)
    (hK : 0 ≤ K) (hC : 0 ≤ Cn) :
    a * r₄ * (1 + x ^ ((1 : ℝ) / 2) * K) ^ (2 * b) * (Cn * (x ^ (k + 1))⁻¹) ≤
      a * ((1 + K) ^ 2) ^ k * Cn * r₄ * x⁻¹ := by
  have hx0 : 0 < x := by linarith
  set s := x ^ ((1 : ℝ) / 2) with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow hx (by norm_num)
  have hs2 : s ^ 2 = x := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have h1 : (1 + s * K) ^ (2 * b) ≤ ((1 + K) ^ 2 * x) ^ k := by
    rw [pow_mul]
    have h2 : (1 + s * K) ^ 2 ≤ (1 + K) ^ 2 * x := by
      rw [← hs2, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
    have h3 : 1 ≤ (1 + K) ^ 2 * x := by
      have : 1 ≤ (1 + K) ^ 2 := one_le_pow₀ (by linarith)
      nlinarith
    calc ((1 + s * K) ^ 2) ^ b ≤ ((1 + K) ^ 2 * x) ^ b := pow_le_pow_left₀ (by positivity) h2 b
      _ ≤ _ := pow_le_pow_right₀ h3 hb
  calc a * r₄ * (1 + s * K) ^ (2 * b) * (Cn * (x ^ (k + 1))⁻¹)
      ≤ a * r₄ * ((1 + K) ^ 2 * x) ^ k * (Cn * (x ^ (k + 1))⁻¹) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
    _ = _ := by
        rw [mul_pow]
        field_simp
        ring
private theorem far_bound (c m x K : ℝ) (hc : 0 < c) (hm : 0 < m) (hx : 0 < x) (hK : 0 ≤ K) (hmx : x ≤ m ^ 50) :
    Real.exp (-(c * (m / 2))) * K ≤ (Nat.factorial 50 : ℝ) * (2 / c) ^ 50 * K * x⁻¹ := by
  have ht : 0 < c * (m / 2) := by positivity
  have h1 := exp_neg_le_factorial_div _ ht 50
  have h2 : (Nat.factorial 50 : ℝ) / (c * (m / 2)) ^ 50 ≤ (Nat.factorial 50 : ℝ) * (2 / c) ^ 50 * x⁻¹ := by
    have e : (c * (m / 2)) ^ 50 = (c / 2) ^ 50 * m ^ 50 := by
      rw [← mul_pow]
      congr 1
      ring
    rw [e, div_le_iff₀ (by positivity)]
    have e2 : (2 / c) ^ 50 * (c / 2) ^ 50 = 1 := by
      rw [← mul_pow]
      have : 2 / c * (c / 2) = 1 := by field_simp
      rw [this, one_pow]
    have h3 : 1 ≤ x⁻¹ * m ^ 50 := by
      rw [inv_mul_eq_div, le_div_iff₀ hx]
      linarith
    have hf : (0 : ℝ) < (Nat.factorial 50 : ℝ) := by positivity
    calc (Nat.factorial 50 : ℝ) = (Nat.factorial 50 : ℝ) * ((2 / c) ^ 50 * (c / 2) ^ 50) * 1 := by rw [e2]; ring
      _ ≤ (Nat.factorial 50 : ℝ) * ((2 / c) ^ 50 * (c / 2) ^ 50) * (x⁻¹ * m ^ 50) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  calc Real.exp (-(c * (m / 2))) * K ≤ ((Nat.factorial 50 : ℝ) * (2 / c) ^ 50 * x⁻¹) * K :=
        mul_le_mul_of_nonneg_right (h1.trans h2) hK
    _ = _ := by ring
private theorem sq_bound_of_le_mul (a r ρ g : ℝ) (ha : 0 ≤ a) (hr1 : 1 ≤ r) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ a * r)
    (hg : 0 ≤ g) :
    2 * (1 + ρ) ^ 2 + g ≤ (2 * (1 + a) ^ 2 + g) * r ^ 2 := by
  have hr2' : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ hr1
  have h1 : 1 + ρ ≤ (1 + a) * r := by nlinarith
  have h2 : (1 + ρ) ^ 2 ≤ (1 + a) ^ 2 * r ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 2
  nlinarith
private theorem le_sq_div_two (a r ρ : ℝ) (ha : 0 ≤ a) (h : 2 * a + 2 ≤ r) (hρ : ρ ≤ a * r) : ρ ≤ r ^ 2 / 2 := by
  nlinarith
private theorem difference_bound (Cd Cy Cm x h r y : ℝ) (b k : ℕ) (hb1 : 1 ≤ b) (hb : b ≤ k)
    (hCm : 0 ≤ Cm) (hCd : 0 ≤ Cd) (hCy : 1 ≤ Cy) (hr : 1 ≤ r) (hy : 1 ≤ y) (hx : 0 < x) (hh : 0 ≤ h)
    (hi : 0 ≤ h * x⁻¹) :
    Cm * r ^ (4 * b) * h * (Cd * r ^ 2 * x⁻¹ * y ^ 2) * (Cy * y) ^ (2 * b - 1) ≤
      Cm * Cd * Cy ^ (2 * k) * (r ^ (4 * b + 2) * (h * x⁻¹) * y ^ (2 * b + 1)) := by
  have e1 : y ^ 2 * y ^ (2 * b - 1) = y ^ (2 * b + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have e2 : r ^ (4 * b) * r ^ 2 = r ^ (4 * b + 2) := (pow_add _ _ _).symm
  have h1 : Cy ^ (2 * b - 1) ≤ Cy ^ (2 * k) := pow_le_pow_right₀ hCy (by omega)
  calc Cm * r ^ (4 * b) * h * (Cd * r ^ 2 * x⁻¹ * y ^ 2) * (Cy * y) ^ (2 * b - 1)
      = Cm * Cd * Cy ^ (2 * b - 1) * ((r ^ (4 * b) * r ^ 2) * (h * x⁻¹) * (y ^ 2 * y ^ (2 * b - 1))) := by
        rw [mul_pow]
        ring
    _ = Cm * Cd * Cy ^ (2 * b - 1) * (r ^ (4 * b + 2) * (h * x⁻¹) * y ^ (2 * b + 1)) := by rw [e1, e2]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) ?_
        positivity
end Bounds
section Norms
variable {m : ℕ} {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
private theorem weightedCurvatureNorm_indicator_sub_le (E : Set Ω) (ω : TorusPlaquette m → ℝ) (q : ENNReal)
    (c₁ c₂ c₃ : Ω → ColourForm m) (Dd K : ℝ) (hK : 0 ≤ K) (Near : OrientedPlaquette m → Prop)
    (hnear : ∀ p, Near p → ENNReal.ofReal (ω p.1) *
      eLpNorm (E.indicator fun η => curlNorm (fun e b => c₃ η e b - c₂ η e b) p.1) q μ ≤ ENNReal.ofReal Dd)
    (hsame : ∀ p, Near p → ∀ η, curlNorm (fun e b => c₁ η e b - c₂ η e b) p.1 =
      curlNorm (fun e b => c₃ η e b - c₂ η e b) p.1)
    (hfar : ∀ p, ¬ Near p → ENNReal.ofReal (ω p.1) * ENNReal.ofReal K ≤ ENNReal.ofReal Dd)
    (hfarb : ∀ p, ¬ Near p → ∀ᵐ η ∂μ, η ∈ E → curlNorm (fun e b => c₁ η e b - c₂ η e b) p.1 ≤ K) :
    weightedCurvatureNorm μ ω q (fun η => E.indicator c₁ η - E.indicator c₂ η) ≤ ENNReal.ofReal Dd := by
  classical
  refine iSup_le fun p => ?_
  have hfun : (fun η => curlNorm (E.indicator c₁ η - E.indicator c₂ η) p.1) =
      E.indicator fun η => curlNorm (fun e b => c₁ η e b - c₂ η e b) p.1 := by
    funext η
    by_cases hη : η ∈ E
    · simp only [Set.indicator_of_mem hη]
      rfl
    · simp only [Set.indicator_of_notMem hη, sub_zero]
      unfold curlNorm curl
      simp
  rw [hfun]
  by_cases hp : Near p
  · have e : (E.indicator fun η => curlNorm (fun e b => c₁ η e b - c₂ η e b) p.1) =
        E.indicator fun η => curlNorm (fun e b => c₃ η e b - c₂ η e b) p.1 := by
      funext η
      by_cases hη : η ∈ E
      · simp only [Set.indicator_of_mem hη, hsame p hp η]
      · simp only [Set.indicator_of_notMem hη]
    rw [e]
    exact hnear p hp
  · refine le_trans (mul_le_mul_right ?_ _) (hfar p hp)
    have h1 : eLpNorm (E.indicator fun η => curlNorm (fun e b => c₁ η e b - c₂ η e b) p.1) q μ ≤
        μ Set.univ ^ q.toReal⁻¹ * ENNReal.ofReal K := by
      refine eLpNorm_le_of_ae_bound ?_
      filter_upwards [hfarb p hp] with η hη
      by_cases hm : η ∈ E
      · simp only [Set.indicator_of_mem hm]
        rw [Real.norm_of_nonneg (show 0 ≤ curlNorm (fun e b => c₁ η e b - c₂ η e b) p.1 from Real.sqrt_nonneg _)]
        exact hη hm
      · simp only [Set.indicator_of_notMem hm, norm_zero]
        exact hK
    simpa using h1
end Norms
section Roots
private theorem le_rpow_inv_hundred (a x : ℝ) (ha : 0 ≤ a) (hx : a ^ 100 ≤ x) : a ≤ x ^ ((1 : ℝ) / 100) := by apply _root_.YangMills.SharedProofs.p61349 <;> assumption
end Roots
end FormProductStep
set_option maxHeartbeats 4000000 in
open FormProductStep in
theorem formProductMeanStepStatement_holds (hAt : cutoffMeanBoundsStatement) (hLaw : coldDensityIntegrableStatement)
    (hCut : goodConfigCutoffStatement) (hMeans : formMeansAtWeightStatement) (hForget : goodStateMeanForgetsStatement)
    (hFine : coldFineFieldStatement) (hMean : fluctuationMeanOfGoodStateStatement)
    (hWin : scaleWindowStatement) (hSites : farLevelSupportSitesStatement)
    (hContr : responseContractionStatement) : formProductMeanStepStatement := by
  unfold cutoffMeanBoundsStatement ForAllPoints at hAt
  unfold coldDensityIntegrableStatement ForAllPoints at hLaw
  unfold goodConfigCutoffStatement ForAllPoints at hCut
  unfold formMeansAtWeightStatement ForAllPoints at hMeans
  unfold goodStateMeanForgetsStatement ForAllPoints at hForget
  unfold coldFineFieldStatement ForAllPoints at hFine
  unfold fluctuationMeanOfGoodStateStatement ForAllPoints at hMean
  unfold scaleWindowStatement ForAllPoints at hWin
  unfold farLevelSupportSitesStatement ForAllPoints at hSites
  unfold formProductMeanStepStatement ForAllPoints
  refine forAllParameters_mono (forAllParameters_and forAllParameters_rate_pos_side
    (forAllParameters_and (forAllParameters_contraction hContr) (forAllParameters_and hAt
    (forAllParameters_and hLaw (forAllParameters_and hCut (forAllParameters_and hMeans
    (forAllParameters_and hForget (forAllParameters_and hFine
    (forAllParameters_and hMean (forAllParameters_and hWin hSites)))))))))) ?_
  rintro Λ ⟨⟨hrate, hL⟩, ⟨θ, hθ, Hθ⟩, ⟨Ca, _, Xa, _, hya, Ha⟩, ⟨_, _, Xl, _, _, Hl⟩, ⟨_, _, Xc, _, _, Hc⟩,
    ⟨Cm, _, Xm, _, _, Hm⟩, ⟨_, _, Xg, _, _, Hg⟩, ⟨Cf, _, Xf, _, _, Hf⟩, ⟨Cv, _, Xv, _, _, Hv⟩,
    ⟨_, _, Xw, _, _, Hw⟩, ⟨Cs, _, _, _, _, Hs⟩⟩
  clear hAt hLaw hCut hMeans hForget hFine hMean hWin hSites hContr
  have hcw : 0 < Λ.stepParams.weightRate / 8 := by positivity
  obtain ⟨Kη, hKη⟩ : ∃ K : ℝ, K = θ * 60 + 8 * |Λ.stepParams.threshold / 64| := ⟨_, rfl⟩
  have hKη0 : 0 ≤ Kη := by rw [hKη]; positivity
  obtain ⟨K₁, hK₁⟩ : ∃ K : ℝ, K = 60 + Kη := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  obtain ⟨Cq, hCq⟩ : ∃ c : ℝ, c = |Cf (8 * Λ.k)| := ⟨_, rfl⟩
  have hCq0 : 0 ≤ Cq := by rw [hCq]; positivity
  obtain ⟨Cy, hCy⟩ : ∃ c : ℝ, c = 1 + 2 * Cq := ⟨_, rfl⟩
  have hCy1 : 1 ≤ Cy := by rw [hCy]; linarith
  obtain ⟨Cw, hCw⟩ : ∃ c : ℝ, c = 2 * (1 + |Cs 0|) ^ 2 + 4 / (Λ.stepParams.weightRate / 8) ^ 2 := ⟨_, rfl⟩
  have hCw0 : 0 ≤ Cw := by rw [hCw]; positivity
  obtain ⟨Cfar, hCfar⟩ : ∃ c : ℝ, c = (Nat.factorial 50 : ℝ) * (2 / (Λ.stepParams.weightRate / 8)) ^ 50 * K₁ :=
    ⟨_, rfl⟩
  have hCfar0 : 0 ≤ Cfar := by rw [hCfar]; positivity
  obtain ⟨Cd, hCd⟩ : ∃ c : ℝ, c = Cq * Cw + Cfar := ⟨_, rfl⟩
  have hCd0 : 0 ≤ Cd := by rw [hCd]; positivity
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = |Ca 0| * 4 ^ Λ.k * ((200 * (Λ.k + 1)).factorial : ℝ) := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℝ, c = |Cm 0| * Cd * Cy ^ (2 * Λ.k) := ⟨_, rfl⟩
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
  obtain ⟨c₃, hc₃⟩ : ∃ c : ℝ, c = |Ca 0| * ((1 + Kη) ^ 2) ^ Λ.k * |Cf (Λ.k + 1)| := ⟨_, rfl⟩
  have hc₃0 : 0 ≤ c₃ := by rw [hc₃]; positivity
  refine ⟨fun _ => c₁ + c₂ + c₃ + |Cv 0|, 1,
    max (max (max Xa Xl) (max Xc Xm)) (max (max Xg Xf) (max (max Xv Xw) (max ((10 : ℝ) ^ 200) ((2 * |Cs 0| + 2) ^ 100)))),
    one_pos, le_trans hya (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))),
    fun S hx d n _ hd hn V Y ω hgood himg B => ?_⟩
  have hmx := fun {a b : ℝ} (h : a ≤ b) (h2 : b ≤ S.scaleCoupling) => le_trans h h2
  have hxL : max (max (max Xa Xl) (max Xc Xm)) (max (max Xg Xf) (max (max Xv Xw)
      (max ((10 : ℝ) ^ 200) ((2 * |Cs 0| + 2) ^ 100)))) ≤ S.scaleCoupling := hx
  have hxl1 := le_trans (le_max_left _ _) hxL
  have hxl2 := le_trans (le_max_right _ _) hxL
  have hxa : Xa ≤ S.scaleCoupling := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxl1
  have hxll : Xl ≤ S.scaleCoupling := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxl1
  have hxc : Xc ≤ S.scaleCoupling := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hxl1
  have hxm : Xm ≤ S.scaleCoupling := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hxl1
  have hxg : Xg ≤ S.scaleCoupling := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxl2
  have hxf : Xf ≤ S.scaleCoupling := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxl2
  have hxr := le_trans (le_max_right _ _) hxl2
  have hxv : Xv ≤ S.scaleCoupling := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxr
  have hxw : Xw ≤ S.scaleCoupling := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxr
  have hxt : (10 : ℝ) ^ 200 ≤ S.scaleCoupling := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hxr
  have hxs : (2 * |Cs 0| + 2) ^ 100 ≤ S.scaleCoupling :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hxr
  have hx0 : 0 < S.scaleCoupling := lt_of_lt_of_le (by positivity) hxt
  have hx1 : 1 ≤ S.scaleCoupling := le_trans (one_le_pow₀ (by norm_num)) hxt
  have hrr : S.range = clusterRange S.scaleCoupling := rfl
  have hrw : S.scaleCoupling ^ ((1 : ℝ) / 100) ≤ (S.range : ℝ) := Nat.le_ceil _
  have hCsr : 2 * |Cs 0| + 2 ≤ (S.range : ℝ) := (le_rpow_inv_hundred _ _ (by positivity) hxs).trans hrw
  have hr1 : (1 : ℝ) ≤ S.range := by
    have := abs_nonneg (Cs 0)
    linarith
  have hr2 : 2 ≤ S.range := by
    have : (2 : ℝ) ≤ S.range := by
      have := abs_nonneg (Cs 0)
      linarith
    exact_mod_cast this
  have hmm : (S.rangeSq : ℝ) = (S.range : ℝ) ^ 2 := by
    show ((S.range ^ 2 : ℕ) : ℝ) = _
    push_cast
    rfl
  have hm2 : 2 ≤ S.rangeSq := hr2.trans (Nat.le_self_pow (by norm_num) _)
  have hm0 : (0 : ℝ) < S.rangeSq := by
    rw [hmm]
    positivity
  have hxm50 : S.scaleCoupling ≤ (S.rangeSq : ℝ) ^ 50 := by
    have e : S.scaleCoupling = (S.scaleCoupling ^ ((1 : ℝ) / 100)) ^ (100 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    rw [hmm, ← pow_mul]
    calc S.scaleCoupling = (S.scaleCoupling ^ ((1 : ℝ) / 100)) ^ (100 : ℕ) := e
      _ ≤ (S.range : ℝ) ^ (2 * 50) := pow_le_pow_left₀ (Real.rpow_nonneg hx0.le _) hrw _
  have hq14 : S.scaleCoupling ^ (-(1 / 4) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  obtain ⟨-, -, hN3, -, -, hKK, hwin⟩ := Hw S hxw
  have hnL : n * Λ.stepParams.side = S.levelSide (S.lastSeparated + d) := by
    rw [hn]
    show S.data.sideAt Λ.stepParams.side (S.lastSeparated + d + 1) * Λ.stepParams.side =
      S.data.sideAt Λ.stepParams.side (S.lastSeparated + d)
    unfold LevelTestFunctions.LevelData.sideAt
    have e : S.data.windowLevel - (S.lastSeparated + d) = (S.data.windowLevel - (S.lastSeparated + d + 1)) + 1 := by
      omega
    rw [e, pow_succ]
    ring
  have hn64 : 64 ≤ n := by
    have h1 := (hwin (S.lastSeparated + d + 1) (by omega) (by omega)).2
    have h2 : Λ.stepParams.side ≤ Λ.stepParams.side ^ S.logIndex := Nat.le_self_pow (by omega) _
    rw [hn]
    omega
  obtain ⟨hcutM, hvM, hB⟩ := Ha S hxa d (n * Λ.stepParams.side) (by omega) hnL
  obtain ⟨hsz, hpc, hbd, hms, hgg, hlc⟩ := hB B
  obtain ⟨hI, hpos⟩ := Hl S hxll d n hd hn V Y hgood
  obtain ⟨hprob, hmeanEq, hballs⟩ := normalizedLaw_facts _ hI hpos
  obtain ⟨fi, fii, fiii⟩ := Hf S hxf d n hd hn V Y hgood
  have hcutUp := Hc S hxc (S.lastSeparated + d + 1) (by omega) (by omega) n hn V Y hgood
  have hcutDown := fun (W : TorusField (n * Λ.stepParams.side)) (Yt : Finset (TorusSite (n * Λ.stepParams.side))) =>
    Hc S hxc (S.lastSeparated + d) (by omega) (by omega) (n * Λ.stepParams.side) hnL W Yt
  have t3 := Hv S hxv d n hd hn V Y hgood B
  set s := coldSettingOver (S.tower.stage (S.lastSeparated + d)).toStepSetup
    (S.smoothedField (S.lastSeparated + d + 1) n V) with hs
  set μ := coldFreeLaw (S.tower.stage (S.lastSeparated + d)).toStepSetup
    (S.smoothedField (S.lastSeparated + d + 1) n V) with hμ
  have : IsProbabilityMeasure μ := hprob
  set o := S.originSite (S.lastSeparated + d) (n * Λ.stepParams.side) with ho
  set E : Set (FreeCoords s.free) := {η | boxCurvature o (2 * S.rangeSq) (s.field η) ≤
    S.scaleCoupling ^ (-(1 / 4) : ℝ)} with hE
  set c₁f : FreeCoords s.free → ColourForm (n * Λ.stepParams.side) := fun η =>
    toColourForm (cutoffCoords Λ.stepParams (s.field η) o S.rangeSq) with hc₁f
  set c₂f : FreeCoords s.free → ColourForm (n * Λ.stepParams.side) := fun η e b =>
    pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d)
      (S.cutoffColourForm (S.lastSeparated + d + 1) n V) e b + freeCoordForm s η e b with hc₂f
  set c₃f : FreeCoords s.free → ColourForm (n * Λ.stepParams.side) := fun η =>
    toColourForm (axialCoords Λ.stepParams (s.field η) o) with hc₃f
  have hEm : MeasurableSet E := by
    have : Measurable fun η : FreeCoords s.free =>
        S.localCurvature (S.lastSeparated + d) (n * Λ.stepParams.side) (s.field η) :=
      hvM.comp (ClusterExpansionOfAStep.ChartSetting.measurable_field s)
    exact this measurableSet_Iic
  have hc₁m : Measurable c₁f := hcutM.comp (ClusterExpansionOfAStep.ChartSetting.measurable_field s)
  have hc₂m : Measurable c₂f := by
    refine measurable_pi_iff.2 fun e => measurable_pi_iff.2 fun b => ?_
    have h := (measurable_pi_iff.1 (measurable_pi_iff.1 (measurable_freeCoordForm s) e)) b
    exact measurable_const.add h
  have hgoodE : ∀ η ∈ E, S.IsGoodConfig (S.lastSeparated + d) (n * Λ.stepParams.side) (s.field η) ∅ := fun η h =>
    ⟨Finset.disjoint_empty_left _, h⟩
  have hnotE : ∀ η, η ∉ E → ¬ S.IsGoodConfig (S.lastSeparated + d) (n * Λ.stepParams.side) (s.field η) ∅ :=
    fun η h hg => h hg.curvature_le
  have hc₂b : ∀ η : FreeCoords s.free,
      (∀ b, coordNorm (η b) < (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius) →
      ∀ p : OrientedPlaquette (n * Λ.stepParams.side), curlNorm (c₂f η) p.1 ≤ Kη := by
    intro η hb p
    have h1 := curlNorm_add_le (pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side (S.lastSeparated + d)
      (S.cutoffColourForm (S.lastSeparated + d + 1) n V)) (freeCoordForm s η) p.1
    have hv1 : S.localCurvature (S.lastSeparated + d + 1) n V ≤ 1 := hgood.curvature_le.trans hq14
    have h2 : ∀ p : OrientedPlaquette n, curlNorm (S.cutoffColourForm (S.lastSeparated + d + 1) n V) p.1 ≤ 60 :=
      fun p => (hcutUp.2.1 p).trans (mul_le_of_le_one_right (by norm_num) hv1)
    have h3 := Hθ (S.lastSeparated + d) n hn64 _ 60 (by norm_num) h2 p
    have h4 : curlNorm (freeCoordForm s η) p.1 ≤ 8 * |Λ.stepParams.threshold / 64| :=
      curlNorm_le_of_abs_le _ _ (abs_nonneg _) (fun e b => abs_freeCoordForm_le s η hb e b) p.1
    rw [hKη]
    exact h1.trans (add_le_add h3 h4)
  have hp1 : ∀ η : FreeCoords s.free, η ∈ E → ∀ p : OrientedPlaquette (n * Λ.stepParams.side),
      curlNorm (c₁f η) p.1 ≤ 60 := by
    intro η h p
    have h1 := (hcutDown (s.field η) ∅ (hgoodE η h)).2.1 p
    have h2 : S.localCurvature (S.lastSeparated + d) (n * Λ.stepParams.side) (s.field η) ≤
        S.scaleCoupling ^ (-(1 / 4) : ℝ) := h
    exact h1.trans (mul_le_of_le_one_right (by norm_num) (h2.trans hq14))
  have hv₁0 : 0 ≤ S.localCurvature (S.lastSeparated + d + 1) n V := Real.iSup_nonneg fun _ => norm_nonneg _
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = S.scaleCoupling ^ ((1 : ℝ) / 2) := ⟨_, rfl⟩
  have hh1 : 1 ≤ h := by
    rw [hh]
    exact Real.one_le_rpow hx1 (by norm_num)
  have hhh : h * h = S.scaleCoupling := by
    rw [hh, ← Real.rpow_add hx0]
    norm_num
  have hhi : S.scaleCoupling ^ (-(1 / 2) : ℝ) = h⁻¹ := by
    rw [Real.rpow_neg hx0.le, ← hh]
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 + h * S.localCurvature (S.lastSeparated + d + 1) n V := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := by
    rw [hy]
    have := mul_nonneg (zero_le_one.trans hh1) hv₁0
    linarith only [this]
  have hy0 : 0 ≤ y := zero_le_one.trans hy1
  have hV2 : (S.localCurvature (S.lastSeparated + d + 1) n V + S.scaleCoupling ^ (-(1 / 2) : ℝ)) ^ 2 =
      S.scaleCoupling⁻¹ * y ^ 2 := by
    rw [hhi, hy, ← hhh]
    have hne0 : h ≠ 0 := (zero_lt_one.trans_le hh1).ne'
    field_simp
    ring
  have hr0 : (0 : ℝ) ≤ S.range := zero_le_one.trans hr1
  have hxi0 : 0 ≤ S.scaleCoupling⁻¹ := by positivity
  obtain ⟨Dd, hDd⟩ : ∃ D : ℝ, D = Cd * (S.range : ℝ) ^ 2 * S.scaleCoupling⁻¹ * y ^ 2 := ⟨_, rfl⟩
  have hDd0 : 0 ≤ Dd := by rw [hDd]; positivity
  have hrd : (S.radius : ℝ) ≤ |Cs 0| * (S.range : ℝ) :=
    ((Hs S).2.1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hr0)
  have hrd0 : (0 : ℝ) ≤ S.radius := by positivity
  have hrdm : (S.radius : ℝ) ≤ (S.rangeSq : ℝ) / 2 := by
    rw [hmm]
    exact le_sq_div_two _ _ _ (abs_nonneg _) hCsr hrd
  have hq8 : ((8 * Λ.k : ℕ) : ENNReal) = 8 * (Λ.k : ENNReal) := by
    push_cast
    rfl
  have h1q : 1 ≤ 8 * Λ.k := by
    have := NeZero.pos Λ.k
    omega
  have hCwr : 2 * (1 + (S.radius : ℝ)) ^ 2 + 4 / (Λ.stepParams.weightRate / 8) ^ 2 ≤ Cw * (S.range : ℝ) ^ 2 := by
    rw [hCw]
    exact sq_bound_of_le_mul _ _ _ _ (abs_nonneg _) hr1 hrd0 hrd (by positivity)
  have hω0 : ∀ p, 0 ≤ S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) p := fun p => (Real.exp_pos _).le
  have hDn : weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side))
      (8 * (Λ.k : ENNReal)) (fun η => E.indicator c₁f η - E.indicator c₂f η) ≤ ENNReal.ofReal Dd := by
    refine weightedCurvatureNorm_indicator_sub_le μ E _ _ c₁f c₂f c₃f Dd K₁ hK₁0
      (fun p => TorusFields.supDist p.1.1 o + 1 ≤ S.rangeSq) ?_
      (fun p hp η => curlNorm_cutoffCoords_sub Λ.stepParams (s.field η) o S.rangeSq hm2 (c₂f η) p.1 hp) ?_ ?_
    · intro p hp
      have hδ2 : (TorusFields.supDist p.1.1 o : ℝ) ≤ 2 * (S.rangeSq : ℝ) := by
        have h1 : ((TorusFields.supDist p.1.1 o + 1 : ℕ) : ℝ) ≤ S.rangeSq := by exact_mod_cast hp
        push_cast at h1
        linarith only [h1, hm0]
      have h1 := fii p (8 * Λ.k) h1q hδ2
      rw [hq8] at h1
      refine (mul_le_mul_right h1 _).trans ?_
      rw [← ENNReal.ofReal_mul (hω0 p.1)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hw := exp_mul_sq_le (Λ.stepParams.weightRate / 8) (TorusFields.supDist p.1.1 o : ℝ) (S.radius : ℝ) hcw
        (by positivity) hrd0
      have hw2 : S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) p.1 *
          (1 + (TorusFields.supDist p.1.1 o : ℝ)) ^ 2 ≤ Cw * (S.range : ℝ) ^ 2 :=
        hw.trans hCwr
      rw [hV2]
      calc S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) p.1 *
            (Cf (8 * Λ.k) * (1 + (TorusFields.supDist p.1.1 o : ℝ)) ^ 2 * (S.scaleCoupling⁻¹ * y ^ 2))
          ≤ S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) p.1 *
            (Cq * (1 + (TorusFields.supDist p.1.1 o : ℝ)) ^ 2 * (S.scaleCoupling⁻¹ * y ^ 2)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_
              (by positivity)) (by positivity)) (hω0 p.1)
            rw [hCq]
            exact le_abs_self _
        _ = Cq * (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) p.1 *
            (1 + (TorusFields.supDist p.1.1 o : ℝ)) ^ 2) * (S.scaleCoupling⁻¹ * y ^ 2) := by ring
        _ ≤ Cq * (Cw * (S.range : ℝ) ^ 2) * (S.scaleCoupling⁻¹ * y ^ 2) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw2 hCq0) (by positivity)
        _ ≤ Dd := by
            rw [hDd, hCd]
            have h5 : 0 ≤ Cfar * (S.range : ℝ) ^ 2 * S.scaleCoupling⁻¹ * y ^ 2 := by positivity
            have e5 : (Cq * Cw + Cfar) * (S.range : ℝ) ^ 2 * S.scaleCoupling⁻¹ * y ^ 2 =
                Cq * (Cw * (S.range : ℝ) ^ 2) * (S.scaleCoupling⁻¹ * y ^ 2) +
                  Cfar * (S.range : ℝ) ^ 2 * S.scaleCoupling⁻¹ * y ^ 2 := by ring
            rw [e5]
            linarith only [h5]
    · intro p hp
      rw [← ENNReal.ofReal_mul (hω0 p.1)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hδ : (S.rangeSq : ℝ) ≤ (TorusFields.supDist p.1.1 o : ℝ) := by
        have : S.rangeSq ≤ TorusFields.supDist p.1.1 o := by
          have := hp
          simp only [not_le] at this
          omega
        exact_mod_cast this
      have hmax : (S.rangeSq : ℝ) / 2 ≤ max 0 ((TorusFields.supDist p.1.1 o : ℝ) - (S.radius : ℝ)) :=
        le_trans (by linarith only [hδ, hrdm]) (le_max_right _ _)
      have hω : S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) p.1 ≤
          Real.exp (-(Λ.stepParams.weightRate / 8 * ((S.rangeSq : ℝ) / 2))) :=
        Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hmax hcw.le))
      have hf := far_bound (Λ.stepParams.weightRate / 8) (S.rangeSq : ℝ) S.scaleCoupling K₁ hcw hm0 hx0 hK₁0 hxm50
      calc S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side) p.1 * K₁ ≤
            Real.exp (-(Λ.stepParams.weightRate / 8 * ((S.rangeSq : ℝ) / 2))) * K₁ :=
            mul_le_mul_of_nonneg_right hω hK₁0
        _ ≤ Cfar * S.scaleCoupling⁻¹ := by rw [hCfar]; exact hf
        _ ≤ Dd := by
            have h1 : Cfar ≤ Cd := by
              rw [hCd]
              have h6 : 0 ≤ Cq * Cw := by positivity
              linarith only [h6]
            have h2 : 1 ≤ (S.range : ℝ) ^ 2 * y ^ 2 := by
              have a1 : 1 ≤ (S.range : ℝ) ^ 2 := one_le_pow₀ hr1
              have a2 : 1 ≤ y ^ 2 := one_le_pow₀ hy1
              exact one_le_mul_of_one_le_of_one_le a1 a2
            rw [hDd]
            calc Cfar * S.scaleCoupling⁻¹ ≤ Cd * S.scaleCoupling⁻¹ * 1 := by
                  rw [mul_one]
                  exact mul_le_mul_of_nonneg_right h1 hxi0
              _ ≤ Cd * S.scaleCoupling⁻¹ * ((S.range : ℝ) ^ 2 * y ^ 2) :=
                  mul_le_mul_of_nonneg_left h2 (by positivity)
              _ = _ := by ring
    · intro p hp
      filter_upwards [hballs] with η hb hηE
      have h1 := curlNorm_sub_le (c₁f η) (c₂f η) p.1
      have h2 := add_le_add (hp1 η hηE p) (hc₂b η hb p)
      rw [hK₁]
      exact h1.trans h2
  have hxi : h * S.scaleCoupling⁻¹ = S.scaleCoupling ^ (-(1 / 2) : ℝ) := by
    rw [hhi, ← hhh]
    have hne0 : h ≠ 0 := (zero_lt_one.trans_le hh1).ne'
    field_simp
  obtain ⟨Pb, hPb⟩ : ∃ P : ℝ, P = (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
      y ^ (2 * B.card + 1) := ⟨_, rfl⟩
  have hPb0 : 0 ≤ Pb := by
    rw [hPb, ← hxi]
    positivity
  have hB : B.card ≤ Λ.k := by simpa using Finset.card_le_univ B
  have hT : ∫⁻ η, ENNReal.ofReal |S.formProductMean d (n * Λ.stepParams.side) B (E.indicator c₁f η) -
      S.formProductMean d (n * Λ.stepParams.side) B (E.indicator c₂f η)| ∂μ ≤ ENNReal.ofReal (c₂ * Pb) := by
    by_cases hBe : B = ∅
    · have hp : ∀ A A' : ColourForm (n * Λ.stepParams.side),
          S.formProductMean d (n * Λ.stepParams.side) B A = S.formProductMean d (n * Λ.stepParams.side) B A' := by
        intro A A'
        rw [hBe]
        simp [MomentPoint.formProductMean, MomentPoint.formProduct]
      have : ∀ η, |S.formProductMean d (n * Λ.stepParams.side) B (E.indicator c₁f η) -
          S.formProductMean d (n * Λ.stepParams.side) B (E.indicator c₂f η)| = 0 := fun η => by
        rw [hp (E.indicator c₁f η) (E.indicator c₂f η), sub_self, abs_zero]
      simp only [this, ENNReal.ofReal_zero, lintegral_zero]
      exact zero_le
    · have hb1 : 1 ≤ B.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hBe)
      obtain ⟨n1, n2⟩ := fiii (8 * Λ.k) h1q
      rw [hq8] at n1 n2
      have hm3 := ((Hm S hxm).1 d (n * Λ.stepParams.side) (by omega) hnL B _ μ (E.indicator c₁f) (E.indicator c₂f)
        (hc₁m.indicator hEm) (hc₂m.indicator hEm)).2.2
      have hCqy : Cf (8 * Λ.k) * (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) *
          S.localCurvature (S.lastSeparated + d + 1) n V) ≤ Cq * y := by
        rw [← hh, ← hy, hCq]
        exact mul_le_mul_of_nonneg_right (le_abs_self _) hy0
      have hYb : 1 + ENNReal.ofReal (S.scaleCoupling ^ ((1 : ℝ) / 2)) *
          (weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side))
              (8 * (Λ.k : ENNReal)) (E.indicator c₁f) +
            weightedCurvatureNorm μ (S.distanceWeight (S.lastSeparated + d) (n * Λ.stepParams.side))
              (8 * (Λ.k : ENNReal)) (E.indicator c₂f)) ≤
          ENNReal.ofReal (Cy * y) := by
        rw [mul_add]
        have a1 := n1.trans (ENNReal.ofReal_le_ofReal hCqy)
        have a2 := n2.trans (ENNReal.ofReal_le_ofReal hCqy)
        have hq0 : 0 ≤ Cq * y := mul_nonneg hCq0 hy0
        calc _ ≤ 1 + (ENNReal.ofReal (Cq * y) + ENNReal.ofReal (Cq * y)) := by gcongr
          _ = ENNReal.ofReal (1 + (Cq * y + Cq * y)) := by
              rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_add hq0 hq0, ENNReal.ofReal_one]
          _ ≤ _ := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [hCy]
              have h5 : 1 * 1 ≤ y := by linarith only [hy1]
              nlinarith only [h5, hq0]
      have ha0 : Cm 0 * (S.range : ℝ) ^ (4 * B.card) * S.scaleCoupling ^ ((1 : ℝ) / 2) ≤
          |Cm 0| * (S.range : ℝ) ^ (4 * B.card) * h := by
        rw [← hh]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
          (zero_le_one.trans hh1)
      have hfin : ENNReal.ofReal (|Cm 0| * (S.range : ℝ) ^ (4 * B.card) * h) * ENNReal.ofReal Dd *
          ENNReal.ofReal (Cy * y) ^ (2 * B.card - 1) ≤ ENNReal.ofReal (c₂ * Pb) := by
        have hh0 : 0 ≤ h := zero_le_one.trans hh1
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hDd, hc₂, hPb, ← hxi]
        exact difference_bound Cd Cy |Cm 0| S.scaleCoupling h (S.range : ℝ) y B.card Λ.k hb1 hB (abs_nonneg _)
          hCd0 hCy1 hr1 hy1 hx0 hh0 (by positivity)
      refine hm3.trans (le_trans ?_ hfin)
      exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal ha0) hDn) (pow_le_pow_left' hYb _)
  obtain ⟨r₄, hr₄⟩ : ∃ r : ℝ, r = (S.range : ℝ) ^ (4 * B.card) := ⟨_, rfl⟩
  have hr₄0 : 0 ≤ r₄ := by rw [hr₄]; positivity
  have hr₄P : r₄ * S.scaleCoupling⁻¹ ≤ Pb := by
    have hxx : S.scaleCoupling⁻¹ ≤ S.scaleCoupling ^ (-(1 / 2) : ℝ) := by
      rw [← hxi]
      exact le_mul_of_one_le_left hxi0 hh1
    have hrr' : r₄ ≤ (S.range : ℝ) ^ (4 * B.card + 2) := by
      rw [hr₄]
      exact pow_le_pow_right₀ hr1 (by omega)
    have hyy : 1 ≤ y ^ (2 * B.card + 1) := one_le_pow₀ hy1
    rw [hPb]
    calc r₄ * S.scaleCoupling⁻¹ ≤ (S.range : ℝ) ^ (4 * B.card + 2) * S.scaleCoupling ^ (-(1 / 2) : ℝ) :=
          mul_le_mul hrr' hxx hxi0 (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (by positivity) (Real.rpow_nonneg hx0.le _)) hyy
  obtain ⟨Mf, hMf⟩ : ∃ M : ℝ, M = |Ca 0| * r₄ * (1 + S.scaleCoupling ^ ((1 : ℝ) / 4)) ^ (2 * B.card) := ⟨_, rfl⟩
  have hbd' : ∀ (W : TorusField (n * Λ.stepParams.side)) (Yt : Finset (TorusSite (n * Λ.stepParams.side))),
      |S.cutoffMean d (n * Λ.stepParams.side) B W Yt| ≤ Mf := by
    intro W Yt
    refine (hbd W Yt).trans ?_
    rw [hMf, hr₄]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      (pow_nonneg (add_nonneg zero_le_one (Real.rpow_nonneg hx0.le _)) _)
  have t1 := Hg S hxg d n hd hn V Y ω hgood himg (fun W Yt => S.cutoffMean d (n * Λ.stepParams.side) B W Yt) Mf hbd'
    hms hgg hlc
  have hT1 : Mf * Real.exp (-(S.scaleCoupling ^ ((1 : ℝ) / 200))) ≤ c₁ * (r₄ * S.scaleCoupling⁻¹) := by
    have := forget_bound S.scaleCoupling hx1 Λ.k B.card hB |Ca 0| r₄ (abs_nonneg _) hr₄0
    rw [hMf, hc₁]
    refine this.trans (le_of_eq ?_)
    ring
  obtain ⟨Mg, hMg⟩ : ∃ M : ℝ, M = |Ca 0| * r₄ * (1 + h * Kη) ^ (2 * B.card) := ⟨_, rfl⟩
  have hMg0 : 0 ≤ Mg := by
    rw [hMg]
    have hh0 : 0 ≤ h := zero_le_one.trans hh1
    positivity
  have hgb : ∀ η : FreeCoords s.free,
      (∀ b, coordNorm (η b) < (S.tower.stage (S.lastSeparated + d)).toStepSetup.ballRadius) →
      |S.formProductMean d (n * Λ.stepParams.side) B (c₂f η)| ≤ Mg := by
    intro η hb
    refine (hsz (c₂f η) Kη hKη0 (hc₂b η hb)).trans ?_
    have hh0 : 0 ≤ h := zero_le_one.trans hh1
    rw [hMg, hr₄, ← hh]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      (by rw [hh]; positivity)
  obtain ⟨eE, heE⟩ : ∃ e : ℝ, e = |Cf (Λ.k + 1)| * (S.scaleCoupling ^ (Λ.k + 1))⁻¹ := ⟨_, rfl⟩
  have heE0 : 0 ≤ eE := by rw [heE]; positivity
  have hEc : μ Eᶜ ≤ ENNReal.ofReal eE := by
    have h1 := fi (Λ.k + 1)
    refine le_trans h1 (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.rpow_neg hx0.le, Real.rpow_natCast, heE]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have hT3 : Mg * eE ≤ c₃ * (r₄ * S.scaleCoupling⁻¹) := by
    have := rare_bound S.scaleCoupling hx1 Λ.k B.card hB |Ca 0| r₄ Kη |Cf (Λ.k + 1)| (abs_nonneg _) hr₄0 hKη0
      (abs_nonneg _)
    rw [hMg, heE, hc₃, hh]
    refine this.trans (le_of_eq ?_)
    ring
  have hG₁E : ∀ η ∈ E, S.cutoffMean d (n * Λ.stepParams.side) B (s.field η) ∅ =
      S.formProductMean d (n * Λ.stepParams.side) B (c₁f η) :=
    fun η h' => if_pos (hgoodE η h')
  have hG₁n : ∀ η, η ∉ E → S.cutoffMean d (n * Λ.stepParams.side) B (s.field η) ∅ = 0 :=
    fun η h' => if_neg (hnotE η h')
  have hcomp := abs_integral_sub_le_of_near μ E hEm
    (fun η => S.cutoffMean d (n * Λ.stepParams.side) B (s.field η) ∅)
    (fun η => S.formProductMean d (n * Λ.stepParams.side) B (c₂f η))
    (fun η => |S.formProductMean d (n * Λ.stepParams.side) B (E.indicator c₁f η) -
      S.formProductMean d (n * Λ.stepParams.side) B (E.indicator c₂f η)|)
    ((hms ∅).comp (ClusterExpansionOfAStep.ChartSetting.measurable_field s)) (hpc.measurable.comp hc₂m) Mf Mg (c₂ * Pb) eE
    (fun η => hbd' _ _) (by filter_upwards [hballs] with η hb using hgb η hb) hMg0
    (by
      filter_upwards [hballs] with η hb
      by_cases hm : η ∈ E
      · simp only [hG₁E η hm, Set.indicator_of_mem hm, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hm),
          add_zero]
        exact le_rfl
      · simp only [hG₁n η hm, Set.indicator_of_mem (Set.mem_compl hm), zero_sub, abs_neg]
        exact (hgb η hb).trans (le_add_of_nonneg_left (abs_nonneg _)))
    hT (mul_nonneg hc₂0 hPb0) hEc heE0
  have hcm₁ : coldExpectation (S.tower.stage (S.lastSeparated + d)).toStepSetup
      (S.smoothedField (S.lastSeparated + d + 1) n V)
      (fun η => S.cutoffMean d (n * Λ.stepParams.side) B (s.field η) ∅) =
      ∫ η, S.cutoffMean d (n * Λ.stepParams.side) B (s.field η) ∅ ∂μ := hmeanEq _
  have hcm₂ : coldExpectation (S.tower.stage (S.lastSeparated + d)).toStepSetup
      (S.smoothedField (S.lastSeparated + d + 1) n V)
      (fun η => S.formProductMean d (n * Λ.stepParams.side) B (c₂f η)) =
      ∫ η, S.formProductMean d (n * Λ.stepParams.side) B (c₂f η) ∂μ := hmeanEq _
  have hT4 : Cv 0 * (S.range : ℝ) ^ (4 * B.card + 1) * S.scaleCoupling ^ (-(1 / 2) : ℝ) *
      (1 + S.scaleCoupling ^ ((1 : ℝ) / 2) * S.localCurvature (S.lastSeparated + d + 1) n V) ^ (2 * B.card) ≤
      |Cv 0| * Pb := by
    rw [← hh, ← hy, hPb, ← hxi]
    have hh0 : 0 ≤ h := zero_le_one.trans hh1
    have a1 : (S.range : ℝ) ^ (4 * B.card + 1) ≤ (S.range : ℝ) ^ (4 * B.card + 2) :=
      pow_le_pow_right₀ hr1 (by omega)
    have a2 : y ^ (2 * B.card) ≤ y ^ (2 * B.card + 1) := pow_le_pow_right₀ hy1 (by omega)
    have a3 : 0 ≤ h * S.scaleCoupling⁻¹ := by positivity
    calc Cv 0 * (S.range : ℝ) ^ (4 * B.card + 1) * (h * S.scaleCoupling⁻¹) * y ^ (2 * B.card)
        ≤ |Cv 0| * (S.range : ℝ) ^ (4 * B.card + 1) * (h * S.scaleCoupling⁻¹) * y ^ (2 * B.card) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
            (by positivity)) a3) (by positivity)
      _ ≤ |Cv 0| * (S.range : ℝ) ^ (4 * B.card + 2) * (h * S.scaleCoupling⁻¹) * y ^ (2 * B.card + 1) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a1 (abs_nonneg _)) a3) a2
            (by positivity) (by positivity)
      _ = _ := by ring
  have hsum : |caseMean (S.tower.stage (S.lastSeparated + d)).toStepSetup
        (hotCoreSites (S.tower.stage (S.lastSeparated + d)).toStepSetup V) V ⟨Y, ω⟩
        (fun W Yt _ _ _ => S.cutoffMean d (n * Λ.stepParams.side) B W Yt) -
      S.formProductMean (d + 1) n B (S.cutoffColourForm (S.lastSeparated + d + 1) n V)| ≤
      (c₁ + c₂ + c₃ + |Cv 0|) * Pb := by
    have h1 := t1.trans hT1
    have h2 : |coldExpectation (S.tower.stage (S.lastSeparated + d)).toStepSetup
        (S.smoothedField (S.lastSeparated + d + 1) n V)
        (fun η => S.cutoffMean d (n * Λ.stepParams.side) B (s.field η) ∅) -
        coldExpectation (S.tower.stage (S.lastSeparated + d)).toStepSetup
        (S.smoothedField (S.lastSeparated + d + 1) n V)
        (fun η => S.formProductMean d (n * Λ.stepParams.side) B (c₂f η))| ≤ c₂ * Pb + Mg * eE := by
      rw [hcm₁, hcm₂]
      exact hcomp
    have h3 := t3.trans hT4
    have e1 := mul_le_mul_of_nonneg_left hr₄P hc₁0
    have e3 := mul_le_mul_of_nonneg_left hr₄P hc₃0
    have tri := abs_sub_le (caseMean (S.tower.stage (S.lastSeparated + d)).toStepSetup
        (hotCoreSites (S.tower.stage (S.lastSeparated + d)).toStepSetup V) V ⟨Y, ω⟩
        (fun W Yt _ _ _ => S.cutoffMean d (n * Λ.stepParams.side) B W Yt))
      (coldExpectation (S.tower.stage (S.lastSeparated + d)).toStepSetup
        (S.smoothedField (S.lastSeparated + d + 1) n V)
        (fun η => S.cutoffMean d (n * Λ.stepParams.side) B (s.field η) ∅))
      (S.formProductMean (d + 1) n B (S.cutoffColourForm (S.lastSeparated + d + 1) n V))
    have tri2 := abs_sub_le (coldExpectation (S.tower.stage (S.lastSeparated + d)).toStepSetup
        (S.smoothedField (S.lastSeparated + d + 1) n V)
        (fun η => S.cutoffMean d (n * Λ.stepParams.side) B (s.field η) ∅))
      (coldExpectation (S.tower.stage (S.lastSeparated + d)).toStepSetup
        (S.smoothedField (S.lastSeparated + d + 1) n V)
        (fun η => S.formProductMean d (n * Λ.stepParams.side) B (c₂f η)))
      (S.formProductMean (d + 1) n B (S.cutoffColourForm (S.lastSeparated + d + 1) n V))
    linarith only [h1, h2, h3, e1, e3, tri, tri2, hT3]
  refine hsum.trans (le_of_eq ?_)
  rw [hPb, hy, hh]
  ring
end MomentLaw
end YangMills.Construction
end
