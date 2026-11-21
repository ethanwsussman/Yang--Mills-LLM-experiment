import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsOneRuleProof
import YangMills.Construction.ClusterExpansionOfAStep.SizeOfTheGaussianOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction
open BlockAverages StepSettings ColdStepAtMirrorFrames
namespace ClusterExpansionOfAStep
namespace GaussianBond
abbrev Euclid3 : Type := EuclideanSpace ℝ (Fin 3)
theorem coordNorm_eq_norm (z : Euclid3) : coordNorm z = ‖z‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
theorem cutoffFactor_le_one {ρ : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ}
    (h0 : 0 ≤ u) : cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_le_one <;> assumption
theorem cutoffFactor_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
def cutGaussian (ρ : ℝ) (p : ℝ → ℝ) (c : ℝ) (z : Euclid3) : ℝ :=
  cutoffFactor ρ p (coordNorm z) * Real.exp (-(c * ‖z‖ ^ 2))
theorem cutGaussian_nonneg (ρ : ℝ) (p : ℝ → ℝ) (c : ℝ) (z : Euclid3) : 0 ≤ cutGaussian ρ p c z :=
  mul_nonneg (cutoffFactor_nonneg _ _ _) (Real.exp_pos _).le
theorem volume_unitBall_pos : 0 < (volume : Measure Euclid3).real (Metric.ball (0 : Euclid3) 1) := by
  refine ENNReal.toReal_pos ?_ measure_ball_lt_top.ne
  exact (Metric.measure_ball_pos volume (0 : Euclid3) one_pos).ne'
theorem volume_closedBall_eq (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure Euclid3).real (Metric.closedBall (0 : Euclid3) r) =
      r ^ 3 * (volume : Measure Euclid3).real (Metric.ball (0 : Euclid3) 1) := by
  unfold Measure.real
  rw [Measure.addHaar_closedBall volume (0 : Euclid3) hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  simp
theorem integral_cutGaussian_le {ρ c : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hc : 0 ≤ c) :
    ∫ z, cutGaussian ρ p c z ≤ ρ ^ 3 * (volume : Measure Euclid3).real (Metric.ball (0 : Euclid3) 1) := by
  have hint : Integrable ((Metric.closedBall (0 : Euclid3) ρ).indicator fun _ => (1 : ℝ)) :=
    IntegrableOn.integrable_indicator (integrableOn_const measure_closedBall_lt_top.ne)
      measurableSet_closedBall
  have hmono : ∫ z, cutGaussian ρ p c z ≤
      ∫ z, (Metric.closedBall (0 : Euclid3) ρ).indicator (fun _ => (1 : ℝ)) z := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (cutGaussian_nonneg ρ p c)) hint
      (Filter.Eventually.of_forall fun z => ?_)
    show cutGaussian ρ p c z ≤ _
    by_cases hz : z ∈ Metric.closedBall (0 : Euclid3) ρ
    · rw [Set.indicator_of_mem hz]
      have h1 := cutoffFactor_le_one hρ hp (norm_nonneg z |>.trans_eq (coordNorm_eq_norm z).symm)
      have h2 : Real.exp (-(c * ‖z‖ ^ 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have := mul_nonneg hc (sq_nonneg ‖z‖); linarith)
      unfold cutGaussian
      nlinarith [Real.exp_pos (-(c * ‖z‖ ^ 2))]
    · rw [Set.indicator_of_notMem hz]
      have hn : ρ < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
      unfold cutGaussian cutoffFactor
      rw [coordNorm_eq_norm, if_neg (by linarith)]
      simp
  rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul, mul_one,
    volume_closedBall_eq ρ hρ.le] at hmono
  exact hmono
theorem le_integral_cutGaussian {ρ c ε : ℝ} {p : ℝ → ℝ} (hρ : 0 < ρ) (hp : IsCutoff ρ p) (hε : 0 ≤ ε)
    (hε' : ε ≤ 5 * ρ / 8) (hc : 0 ≤ c) (hint : Integrable (cutGaussian ρ p c)) :
    Real.exp (-(c * ε ^ 2)) * (ε ^ 3 * (volume : Measure Euclid3).real (Metric.ball (0 : Euclid3) 1)) ≤
      ∫ z, cutGaussian ρ p c z := by
  have hind : Integrable
      ((Metric.closedBall (0 : Euclid3) ε).indicator fun _ => Real.exp (-(c * ε ^ 2))) :=
    IntegrableOn.integrable_indicator (integrableOn_const measure_closedBall_lt_top.ne)
      measurableSet_closedBall
  have hmono : ∫ z, (Metric.closedBall (0 : Euclid3) ε).indicator (fun _ => Real.exp (-(c * ε ^ 2))) z ≤
      ∫ z, cutGaussian ρ p c z := by
    refine integral_mono hind hint fun z => ?_
    by_cases hz : z ∈ Metric.closedBall (0 : Euclid3) ε
    · rw [Set.indicator_of_mem hz]
      have hn : ‖z‖ ≤ ε := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
      unfold cutGaussian cutoffFactor
      rw [coordNorm_eq_norm, if_pos (by linarith), hp.vanish_small _ (norm_nonneg z) (by linarith)]
      simp only [neg_zero, Real.exp_zero, one_mul]
      refine Real.exp_le_exp.mpr ?_
      have : ‖z‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hn 2
      nlinarith
    · rw [Set.indicator_of_notMem hz]
      exact cutGaussian_nonneg _ _ _ _
  rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul,
    volume_closedBall_eq ε hε] at hmono
  linarith [mul_comm (ε ^ 3 * (volume : Measure Euclid3).real (Metric.ball (0 : Euclid3) 1))
    (Real.exp (-(c * ε ^ 2)))]
end GaussianBond
open GaussianBond in
theorem gaussianLogMassLeLog_holds : GaussianLogMassLeLog := by
  intro lam ρ p hlam hρ hp
  set v := (volume : Measure Euclid3).real (Metric.ball (0 : Euclid3) 1) with hv
  have hv0 : 0 < v := volume_unitBall_pos
  set A := |Real.log (ρ ^ 3 * v)| with hA
  set Bv := |Real.log v| with hBv
  refine ⟨A + Bv + lam / 2 + 2, max (Real.exp 1) ((8 / (5 * ρ)) ^ 2), by positivity,
    fun R hρR hpR hx => ?_⟩
  have hx1 : Real.exp 1 ≤ R.coupling := (le_max_left _ _).trans hx
  have hx2 : (8 / (5 * ρ)) ^ 2 ≤ R.coupling := (le_max_right _ _).trans hx
  have hxpos : 0 < R.coupling := (Real.exp_pos 1).trans_le hx1
  have hlog1 : 1 ≤ Real.log R.coupling := by
    have := Real.log_le_log (Real.exp_pos 1) hx1
    rwa [Real.log_exp] at this
  have hc0 : StepSetup.gaussianLogMass R lam =
      Real.log (∫ z, cutGaussian ρ p (R.coupling * lam / 2) z) := by
    unfold StepSetup.gaussianLogMass cutGaussian
    rw [hρR, hpR]
  rw [hc0]
  have hCpos : 0 ≤ A + Bv + lam / 2 + 2 := by positivity
  by_cases hint : Integrable (cutGaussian ρ p (R.coupling * lam / 2))
  · set ε := (Real.sqrt R.coupling)⁻¹ with hε
    have hs : 0 < Real.sqrt R.coupling := Real.sqrt_pos.mpr hxpos
    have hε0 : 0 < ε := inv_pos.mpr hs
    have hε2 : ε ^ 2 = R.coupling⁻¹ := by
      rw [hε, inv_pow, Real.sq_sqrt hxpos.le]
    have hεle : ε ≤ 5 * ρ / 8 := by
      have hsq : 8 / (5 * ρ) ≤ Real.sqrt R.coupling := by
        apply Real.le_sqrt_of_sq_le hx2
      rw [hε]
      have h8 : 0 < 8 / (5 * ρ) := by positivity
      have := inv_anti₀ h8 hsq
      have e : (8 / (5 * ρ))⁻¹ = 5 * ρ / 8 := by
        rw [inv_div]
      linarith
    have hlow := le_integral_cutGaussian hρ hp hε0.le hεle (c := R.coupling * lam / 2) (by positivity) hint
    have hup := integral_cutGaussian_le hρ hp (c := R.coupling * lam / 2) (by positivity)
    have hcε : R.coupling * lam / 2 * ε ^ 2 = lam / 2 := by
      rw [hε2]
      field_simp
    rw [hcε] at hlow
    have hIpos : 0 < Real.exp (-(lam / 2)) * (ε ^ 3 * v) := by positivity
    have hl1 := Real.log_le_log hIpos hlow
    have hl2 := Real.log_le_log (hIpos.trans_le hlow) hup
    have hlogε : Real.log ε = -(Real.log R.coupling / 2) := by
      rw [hε, Real.log_inv, Real.log_sqrt hxpos.le]
    have hexp : Real.log (Real.exp (-(lam / 2)) * (ε ^ 3 * v)) =
        -(lam / 2) + (3 * Real.log ε + Real.log v) := by
      rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
        Real.log_mul (by positivity) hv0.ne', Real.log_pow]
      norm_num
    rw [hexp, hlogε] at hl1
    have a1 : Real.log (ρ ^ 3 * v) ≤ A := le_abs_self _
    have a2 : -Bv ≤ Real.log v := neg_abs_le _
    have hA0 : 0 ≤ A := abs_nonneg _
    have hB0 : 0 ≤ Bv := abs_nonneg _
    rw [abs_le]
    constructor <;> nlinarith
  · rw [integral_undef hint]
    simp only [Real.log_zero, abs_zero]
    positivity
end ClusterExpansionOfAStep
end YangMills.Construction
end
