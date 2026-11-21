import YangMills.Construction.ClusterExpansionOfAStep.ConditionalLawsOfAWeight
import YangMills.Construction.ClusterExpansionOfAStep.GasIsAWeight
import YangMills.Construction.ResponseInTheExpansion.CovarianceByTwoTilts
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory YangMills.Construction.Dobrushin
open scoped ENNReal
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses RenormalizationStepParameters StepSettings StepGas ClusterExpansionOfAStep
namespace TwoTilts
section TiltedLaws
set_option linter.unusedSectionVars false
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)] {A : PairConstraint S}
  {m : ∀ i, Measure (S i)} [∀ i, SigmaFinite (m i)] {W Y F : (∀ i, S i) → ℝ}
private theorem integral_mul_eq_under_tilt (hA : MeasurableSet {σ | A.IsAdmissible σ}) (hW : Measurable W)
    (hWpos : ∀ σ, A.IsAdmissible σ → 0 < W σ) (hY : Measurable Y) (hYone : ∀ σ, A.IsAdmissible σ → 1 ≤ Y σ)
    [hprob : IsProbabilityMeasure (A.gibbsLaw m W)] (hadm : ∀ᵐ σ ∂A.gibbsLaw m W, A.IsAdmissible σ)
    (hYint : Integrable Y (A.gibbsLaw m W)) (hFYint : Integrable (fun σ => F σ * Y σ) (A.gibbsLaw m W)) :
    Integrable F (A.gibbsLaw m fun σ => W σ * Y σ) ∧
      ∫ σ, F σ * Y σ ∂A.gibbsLaw m W = (∫ σ, Y σ ∂A.gibbsLaw m W) * ∫ σ, F σ ∂A.gibbsLaw m fun σ => W σ * Y σ := by
  classical
  set π := Measure.pi m with hπ
  set d := A.weightDensity W with hd
  set dY := A.weightDensity fun σ => W σ * Y σ with hdY
  have hd_meas : Measurable d := by
    rw [hd]
    unfold PairConstraint.weightDensity
    exact Measurable.ite hA (ENNReal.measurable_ofReal.comp hW) measurable_const
  set g : (∀ i, S i) → ℝ≥0∞ := fun σ => ENNReal.ofReal (Y σ) with hg
  have hg_meas : Measurable g := hY.ennreal_ofReal
  set a := ∫⁻ σ, d σ ∂π with ha
  have hmass : a⁻¹ * a = 1 ∧ a ≠ 0 ∧ a ≠ ⊤ := by
    have h1 := hprob.measure_univ
    have e : A.gibbsLaw m W = a⁻¹ • π.withDensity d := rfl
    rw [e] at h1
    simp only [Measure.smul_apply, smul_eq_mul] at h1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    refine ⟨h1, ?_, ?_⟩
    · intro h0
      rw [← ha, h0] at h1
      simp at h1
    · intro ht
      rw [← ha, ht] at h1
      simp at h1
  obtain ⟨-, ha0, hatop⟩ := hmass
  have hprod : dY = d * g := by
    funext σ
    simp only [hdY, hd, hg, Pi.mul_apply, PairConstraint.weightDensity]
    by_cases h : A.IsAdmissible σ
    · rw [if_pos h, if_pos h, ENNReal.ofReal_mul (hWpos σ h).le]
    · rw [if_neg h, if_neg h, zero_mul]
  have hbase : π.withDensity d = a • A.gibbsLaw m W := by
    show π.withDensity d = a • (a⁻¹ • π.withDensity d)
    rw [smul_smul, ENNReal.mul_inv_cancel ha0 hatop, one_smul]
  set μ := A.gibbsLaw m W with hμ
  have hYnonneg : 0 ≤ᵐ[μ] Y := by
    filter_upwards [hadm] with σ hσ
    exact zero_le_one.trans (hYone σ hσ)
  set Gm := ∫⁻ σ, g σ ∂μ with hGm
  have hGm_top : Gm ≠ ⊤ := by
    have := (hasFiniteIntegral_iff_ofReal hYnonneg).mp hYint.hasFiniteIntegral
    exact this.ne
  have hGm_one : 1 ≤ Gm := by
    calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂μ := by simp
      _ ≤ Gm := by
        refine lintegral_mono_ae ?_
        filter_upwards [hadm] with σ hσ
        simpa [hg] using ENNReal.one_le_ofReal.mpr (hYone σ hσ)
  have hGm_zero : Gm ≠ 0 := fun h => by
    rw [h] at hGm_one
    simp at hGm_one
  set b := ∫⁻ σ, dY σ ∂π with hb
  have hb_eq : b = a * Gm := by
    rw [hb, hprod, ← lintegral_withDensity_eq_lintegral_mul π hd_meas hg_meas, hbase, lintegral_smul_measure]
    rfl
  have hb0 : b ≠ 0 := by
    rw [hb_eq]
    exact mul_ne_zero ha0 hGm_zero
  have hbtop : b ≠ ⊤ := by
    rw [hb_eq]
    exact ENNReal.mul_ne_top hatop hGm_top
  set c : ℝ≥0∞ := b⁻¹ * a with hc
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.mpr hbtop) ha0
  have hctop : c ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hb0) hatop
  have htilt : A.gibbsLaw m (fun σ => W σ * Y σ) = c • μ.withDensity g := by
    show b⁻¹ • π.withDensity dY = _
    rw [hprod, withDensity_mul _ hd_meas hg_meas, hbase, withDensity_smul_measure, smul_smul]
  have hcGm : c * Gm = 1 := by
    rw [hc, mul_assoc, ← hb_eq]
    exact ENNReal.inv_mul_cancel hb0 hbtop
  have hYint_eq : ∫ σ, Y σ ∂μ = Gm.toReal :=
    integral_eq_lintegral_of_nonneg_ae hYnonneg hY.aestronglyMeasurable
  have hcY : c.toReal * ∫ σ, Y σ ∂μ = 1 := by
    rw [hYint_eq, ← ENNReal.toReal_mul, hcGm]
    simp
  have hg_lt : ∀ᵐ σ ∂μ, g σ < ⊤ := Filter.Eventually.of_forall fun σ => ENNReal.ofReal_lt_top
  have hg_toReal : ∀ᵐ σ ∂μ, (g σ).toReal = Y σ := by
    filter_upwards [hadm] with σ hσ
    exact ENNReal.toReal_ofReal (zero_le_one.trans (hYone σ hσ))
  have hcongr : (fun σ => (g σ).toReal • F σ) =ᵐ[μ] fun σ => F σ * Y σ := by
    filter_upwards [hg_toReal] with σ hσ
    rw [hσ, smul_eq_mul, mul_comm]
  have hFdens : Integrable F (μ.withDensity g) :=
    (integrable_withDensity_iff_integrable_smul' hg_meas hg_lt).mpr (hFYint.congr hcongr.symm)
  refine ⟨?_, ?_⟩
  · rw [htilt]
    exact (integrable_smul_measure hc0 hctop).mpr hFdens
  · have hF_eq : ∫ σ, F σ ∂(A.gibbsLaw m fun σ => W σ * Y σ) = c.toReal * ∫ σ, F σ * Y σ ∂μ := by
      rw [htilt, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hg_meas hg_lt, integral_congr_ae hcongr]
      rfl
    rw [hF_eq, ← mul_assoc, mul_comm (∫ σ, Y σ ∂μ), hcY, one_mul]
end TiltedLaws
private theorem abs_covariance_le_of_tilts {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {u Yp Yy : Ω → ℝ} {n₁ n₂ : ℝ}
    (hbd : ∀ᵐ σ ∂μ, 1 ≤ Yp σ ∧ |Yy σ| ≤ Yp σ) (hYp : Integrable Yp μ) (hYy : Integrable Yy μ)
    (huYp : Integrable (fun σ => u σ * Yp σ) μ) (huYy : Integrable (fun σ => u σ * Yy σ) μ)
    (h₁ : ∫ σ, u σ * (2 * Yp σ + Yy σ) ∂μ = (∫ σ, (2 * Yp σ + Yy σ) ∂μ) * n₁)
    (h₂ : ∫ σ, u σ * (2 * Yp σ) ∂μ = (∫ σ, 2 * Yp σ ∂μ) * n₂) :
    |∫ σ, u σ * Yy σ ∂μ - (∫ σ, u σ ∂μ) * ∫ σ, Yy σ ∂μ| ≤
      3 * (∫ σ, Yp σ ∂μ) * (|n₁ - ∫ σ, u σ ∂μ| + |n₂ - ∫ σ, u σ ∂μ|) := by
  have f1 : ∫ σ, (2 * Yp σ + Yy σ) ∂μ = 2 * (∫ σ, Yp σ ∂μ) + ∫ σ, Yy σ ∂μ := by
    rw [integral_add (hYp.const_mul 2) hYy, integral_const_mul]
  have f2 : ∫ σ, 2 * Yp σ ∂μ = 2 * ∫ σ, Yp σ ∂μ := integral_const_mul _ _
  have f3 : ∫ σ, u σ * (2 * Yp σ) ∂μ = 2 * ∫ σ, u σ * Yp σ ∂μ := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun σ => by simp only; ring)
  have f4 : ∫ σ, u σ * (2 * Yp σ + Yy σ) ∂μ = 2 * (∫ σ, u σ * Yp σ ∂μ) + ∫ σ, u σ * Yy σ ∂μ := by
    rw [← integral_const_mul, ← integral_add (huYp.const_mul 2) huYy]
    exact integral_congr_ae (Filter.Eventually.of_forall fun σ => by simp only; ring)
  have hP : 0 ≤ ∫ σ, Yp σ ∂μ := integral_nonneg_of_ae (hbd.mono fun σ h => zero_le_one.trans h.1)
  have hQ : |∫ σ, Yy σ ∂μ| ≤ ∫ σ, Yp σ ∂μ := by
    refine (abs_integral_le_integral_abs).trans ?_
    exact integral_mono_ae hYy.abs hYp (hbd.mono fun σ h => h.2)
  rw [f1, f4] at h₁
  rw [f2, f3] at h₂
  set P := ∫ σ, Yp σ ∂μ
  set Q := ∫ σ, Yy σ ∂μ
  set U := ∫ σ, u σ * Yp σ ∂μ
  set V := ∫ σ, u σ * Yy σ ∂μ
  set mean := ∫ σ, u σ ∂μ
  have hQ' := abs_le.mp hQ
  have e : V - mean * Q = (2 * P + Q) * (n₁ - mean) - 2 * P * (n₂ - mean) := by linarith
  rw [e]
  calc _ ≤ |(2 * P + Q) * (n₁ - mean)| + |2 * P * (n₂ - mean)| := abs_sub _ _
    _ = (2 * P + Q) * |n₁ - mean| + 2 * P * |n₂ - mean| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 2 * P + Q), abs_of_nonneg (by positivity : 0 ≤ 2 * P)]
    _ ≤ 3 * P * |n₁ - mean| + 3 * P * |n₂ - mean| := by
        have a1 := mul_le_mul_of_nonneg_right (by linarith : 2 * P + Q ≤ 3 * P) (abs_nonneg (n₁ - mean))
        have a2 := mul_le_mul_of_nonneg_right (by linarith : 2 * P ≤ 3 * P) (abs_nonneg (n₂ - mean))
        exact add_le_add a1 a2
    _ = _ := by ring
end TwoTilts
theorem covarianceByTwoTilts_of_gas (hw : ClusterExpansionOfAStep.GasIsActivityBounded) (hC : Dobrushin.ActivityConditionalLawsStatement) :
    covarianceByTwoTiltsStatement := by
  unfold covarianceByTwoTiltsStatement HoldsAtEveryStep
  obtain ⟨r, p, H⟩ := hw
  refine ⟨r, p, fun T hT hrt K => ?_⟩
  obtain ⟨y₁, H⟩ := H T hT hrt
  refine ⟨max y₁ (200 * T.B), fun y hy R A _ hAT n _ G hG mm Yy Yp hYy_meas hYp_meas hb hmm hYp hmmYp => ?_⟩
  have hOT := hAT.onFamily
  have hnext : R.nextCoupling ≤ 1.01 * R.coupling := by
    have h1 := (abs_le.mp hAT.abs_sub_le).2
    have h2 : 200 * T.B ≤ y := (le_max_right _ _).trans hy
    have h3 := hOT.le_coupling
    linarith only [h1, h2, h3]
  have hwt : G.pairConstraint.IsActivityBounded (G.referenceMeasure ∅) G.weight (G.spinActivity T.gasRate) :=
    H y ((le_max_left _ _).trans hy) R hOT hnext n G hG fun j => j.1.Touches ∅
  obtain ⟨hprob, hgibbs, -, -⟩ := hC G.GasSpin G.SpinValue G.pairConstraint (G.referenceMeasure ∅) _ _ hwt
  have hadm : ∀ᵐ σ ∂(G.gibbsLaw ∅), G.pairConstraint.IsAdmissible σ := hgibbs.ae_admissible
  have hbd : ∀ᵐ σ ∂(G.gibbsLaw ∅), 1 ≤ Yp σ ∧ |Yy σ| ≤ Yp σ := hadm.mono fun σ h => hb σ h
  have hYy : Integrable Yy (G.gibbsLaw ∅) :=
    hYp.mono' hYy_meas.aestronglyMeasurable (hbd.mono fun σ h => by simpa [Real.norm_eq_abs] using h.2)
  have hmmYy : Integrable (fun σ => mm σ * Yy σ) (G.gibbsLaw ∅) := by
    refine hmmYp.mono (hmm.aestronglyMeasurable.mul hYy_meas.aestronglyMeasurable) (hbd.mono fun σ h => ?_)
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact h.2.trans (le_abs_self _)
  have i1 : Integrable (fun σ => 2 * Yp σ + Yy σ) (G.gibbsLaw ∅) := (hYp.const_mul 2).add hYy
  have i2 : Integrable (fun σ => 2 * Yp σ) (G.gibbsLaw ∅) := hYp.const_mul 2
  have iu1 : Integrable (fun σ => mm σ * (2 * Yp σ + Yy σ)) (G.gibbsLaw ∅) := by
    refine ((hmmYp.const_mul 2).add hmmYy).congr (Filter.Eventually.of_forall fun σ => ?_)
    simp only [Pi.add_apply]
    ring
  have iu2 : Integrable (fun σ => mm σ * (2 * Yp σ)) (G.gibbsLaw ∅) := by
    refine (hmmYp.const_mul 2).congr (Filter.Eventually.of_forall fun σ => ?_)
    simp only
    ring
  have o1 : ∀ σ, G.pairConstraint.IsAdmissible σ → 1 ≤ 2 * Yp σ + Yy σ := fun σ h => by
    have h1 := hb σ h
    have h2 := (abs_le.mp h1.2).1
    linarith only [h1.1, h2]
  have o2 : ∀ σ, G.pairConstraint.IsAdmissible σ → 1 ≤ 2 * Yp σ := fun σ h => by
    have h1 := hb σ h
    linarith only [h1.1]
  have q1 : IsProbabilityMeasure (G.pairConstraint.gibbsLaw (G.referenceMeasure ∅) G.weight) := hprob
  obtain ⟨t1, r1⟩ := TwoTilts.integral_mul_eq_under_tilt (m := G.referenceMeasure ∅) (W := G.weight) (F := mm)
    hwt.measurableSet_admissible hwt.measurable hwt.pos_of_admissible
    ((measurable_const.mul hYp_meas).add hYy_meas) o1 hadm i1 iu1
  obtain ⟨t2, r2⟩ := TwoTilts.integral_mul_eq_under_tilt (m := G.referenceMeasure ∅) (W := G.weight) (F := mm)
    hwt.measurableSet_admissible hwt.measurable hwt.pos_of_admissible
    (measurable_const.mul hYp_meas) o2 hadm i2 iu2
  exact ⟨hmmYy, hYy, t1, t2, TwoTilts.abs_covariance_le_of_tilts hbd hYp hYy hmmYp hmmYy r1 r2⟩
end YangMills.Construction.ResponseInTheExpansion
end
