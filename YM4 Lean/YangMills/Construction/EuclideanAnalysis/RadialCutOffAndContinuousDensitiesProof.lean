import YangMills.Construction.EuclideanAnalysis.RadialCutOffAndContinuousDensities
import Mathlib
open MeasureTheory TopologicalSpace
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis.BumpAndDensities
theorem existsRadialBump_holds : ExistsRadialBump := by
  let b : RealSpace 4 → ℝ := fun y => Real.smoothTransition (2 - 4 * ‖y‖ ^ 2)
  have hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))
  have hsupp : Function.support b ⊆ Metric.closedBall 0 (3 / 4) := by
    intro y hy
    rw [mem_closedBall_zero_iff]
    by_contra hbig
    refine hy (Real.smoothTransition.zero_of_nonpos ?_)
    nlinarith [not_le.mp hbig]
  have htsupp : tsupport b ⊆ Metric.closedBall 0 (3 / 4) :=
    closure_minimal hsupp Metric.isClosed_closedBall
  refine ⟨⟨b, hb, ?_, ?_⟩, ?_, fun y => ⟨?_, ?_⟩, fun y hy => ?_⟩
  · exact HasCompactSupport.intro (isCompact_closedBall 0 (3 / 4)) fun y hy => by
      by_contra hne
      exact hy (hsupp hne)
  · exact htsupp.trans (Metric.closedBall_subset_ball (by norm_num))
  · intro y z hyz
    change b y = b z
    simp only [b, hyz]
  · exact Real.smoothTransition.nonneg _
  · exact Real.smoothTransition.le_one _
  · refine Real.smoothTransition.one_of_one_le ?_
    have hn : 0 ≤ ‖y‖ := norm_nonneg y
    nlinarith
def ofRealTest (b : RealSpace 4 → ℝ) (hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b)
    (hc : HasCompactSupport b) : SmoothTestFunction where
  toFun y := (b y : ℂ)
  contDiff' := Complex.ofRealCLM.contDiff.comp hb
  hasCompactSupport' := hc.comp_left Complex.ofReal_zero
  tsupport_subset' := by simp
theorem continuousEqZeroOfIntegralMul_holds : ContinuousEqZeroOfIntegralMul := by
  intro u hu hint
  have hae : ∀ᵐ y ∂(volume : Measure (RealSpace 4)), u y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hu.locallyIntegrable fun b hb hc => ?_
    have h := hint (ofRealTest b hb hc)
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change b y • u y = u y * (b y : ℂ)
    rw [Complex.real_smul, mul_comm]
  have hu0 : u = fun _ => 0 := (Continuous.ae_eq_iff_eq volume hu continuous_const).mp hae
  exact fun y => congrFun hu0 y
theorem mulNormSqLog_eq_mul (φ : RealSpace 4 → ℂ) :
    mulNormSqLog φ = fun y => φ y * ((‖y‖ * (‖y‖ * Real.log ‖y‖) : ℝ) : ℂ) := by
  funext y
  by_cases hy : y = 0
  · simp [mulNormSqLog, hy]
  · simp only [mulNormSqLog, hy, if_false]
    congr 2
    ring
theorem mulNormSqLogContinuous_holds : MulNormSqLogContinuous := by
  intro φ hφ
  have hc : Continuous (mulNormSqLog φ) := by
    rw [mulNormSqLog_eq_mul]
    exact hφ.mul (Complex.continuous_ofReal.comp
      (continuous_norm.mul (Real.continuous_mul_log.comp continuous_norm)))
  exact ⟨hc, hc.locallyIntegrable⟩
theorem combined_holds : Combined :=
  ⟨existsRadialBump_holds, continuousEqZeroOfIntegralMul_holds, mulNormSqLogContinuous_holds⟩
end YangMills.Construction.EuclideanAnalysis.BumpAndDensities
