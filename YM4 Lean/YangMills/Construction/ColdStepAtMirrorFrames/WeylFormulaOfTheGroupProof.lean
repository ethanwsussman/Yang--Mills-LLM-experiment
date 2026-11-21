import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.HaarMeasureInLogarithmicCoordinates
import YangMills.Construction.ColdStepAtMirrorFrames.WeylFormulaOfTheGroup
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps MeasureTheory Set Real Metric
namespace ColdStepAtMirrorFrames
namespace WeylFormula
abbrev ImagSpace : Type := EuclideanSpace ℝ (Fin 3)
theorem norm_toImaginary (v : ImagSpace) :
    ‖((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
theorem re_expUnit_toImaginary (v : ImagSpace) :
    ((expUnit (toImaginary v) : UnitQuaternion) : ℍ[ℝ]).re = cos ‖v‖ := by
  show (NormedSpace.exp ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])).re = _
  rw [Quaternion.exp_of_re_eq_zero _ (toImaginary v).2, norm_toImaginary]
  have hre : ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := (toImaginary v).2
  simp [hre]
def radialIntegrand (φ : ℝ → ℝ) (r : ℝ) : ℝ :=
  (if r < π then sinc r ^ 2 / (2 * π ^ 2) else 0) * φ (1 - cos r)
theorem haarLogDensity_mul_eq_radialIntegrand (φ : ℝ → ℝ) (v : ImagSpace) :
    haarLogDensity v * φ (1 - ((expUnit (toImaginary v) : UnitQuaternion) : ℍ[ℝ]).re) =
      radialIntegrand φ ‖v‖ := by
  rw [re_expUnit_toImaginary]
  rfl
theorem volume_real_unitBall : (volume : Measure ImagSpace).real (ball 0 1) = π * 4 / 3 := by
  rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
  simp
  positivity
theorem integral_Ioi_sq_mul_radialIntegrand (φ : ℝ → ℝ) :
    ∫ r in Ioi (0 : ℝ), r ^ 2 * radialIntegrand φ r =
      ∫ r in (0 : ℝ)..π, sin r ^ 2 / (2 * π ^ 2) * φ (1 - cos r) := by
  rw [intervalIntegral.integral_of_le pi_pos.le, ← integral_indicator measurableSet_Ioc,
    ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  by_cases hpos : 0 < r
  · rw [indicator_of_mem (mem_Ioi.mpr hpos)]
    rcases lt_trichotomy r π with h | h | h
    · rw [indicator_of_mem (show r ∈ Ioc 0 π from ⟨hpos, h.le⟩)]
      simp only [radialIntegrand, if_pos h, sinc_of_ne_zero hpos.ne']
      field_simp
    · subst h
      rw [indicator_of_mem (show π ∈ Ioc 0 π from ⟨hpos, le_rfl⟩)]
      simp [radialIntegrand]
    · rw [indicator_of_notMem (fun hm => absurd hm.2 (not_le.mpr h))]
      simp [radialIntegrand, not_lt.mpr h.le]
  · rw [indicator_of_notMem (by simpa using hpos), indicator_of_notMem (fun hm => hpos hm.1)]
theorem integral_haarRealPartDensity_eq_integral_cos {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∫ t in (0 : ℝ)..2, φ t * haarRealPartDensity t =
      ∫ r in (0 : ℝ)..π, φ (1 - cos r) * haarRealPartDensity (1 - cos r) * sin r := by
  have hcont : Continuous fun t => φ t * haarRealPartDensity t := by
    unfold haarRealPartDensity
    fun_prop
  have h := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := π) (f := fun r => 1 - cos r)
    (f' := sin) (g := fun t => φ t * haarRealPartDensity t)
    (fun r _ => by simpa using (hasDerivAt_cos r).const_sub 1) continuous_sin.continuousOn hcont
  simp only [Function.comp, cos_zero, cos_pi, sub_self] at h
  norm_num at h
  exact h.symm
theorem haarRealPartDensity_one_sub_cos_mul_sin {r : ℝ} (h0 : 0 ≤ r) (hπ : r ≤ π) :
    haarRealPartDensity (1 - cos r) * sin r = 2 / π * sin r ^ 2 := by
  have hs : 0 ≤ sin r := sin_nonneg_of_nonneg_of_le_pi h0 hπ
  have : 2 * (1 - cos r) - (1 - cos r) ^ 2 = sin r ^ 2 := by
    nlinarith [sin_sq_add_cos_sq r]
  unfold haarRealPartDensity
  rw [this, Real.sqrt_sq hs]
  ring
end WeylFormula
open WeylFormula in
theorem weylIntegrationFormula_holds (hH : HaarIntegralInLogCoords) :
    WeylIntegrationFormula := by
  have hlaw : ∀ φ : ℝ → ℝ, Continuous φ →
      ∫ g : UnitQuaternion, φ (1 - ((g : UnitQuaternion) : ℍ[ℝ]).re) ∂haarUnit =
        ∫ t in (0 : ℝ)..2, φ t * haarRealPartDensity t := by
    intro φ hφ
    have hc : Continuous fun g : UnitQuaternion => φ (1 - ((g : UnitQuaternion) : ℍ[ℝ]).re) := by
      refine hφ.comp (continuous_const.sub ?_)
      exact Quaternion.continuous_re.comp continuous_subtype_val
    rw [hH _ hc]
    simp only [haarLogDensity_mul_eq_radialIntegrand]
    rw [integral_fun_norm_addHaar (volume : Measure ImagSpace) (radialIntegrand φ),
      volume_real_unitBall]
    simp only [finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul]
    rw [show (3 - 1 : ℕ) = 2 from rfl, integral_Ioi_sq_mul_radialIntegrand,
      integral_haarRealPartDensity_eq_integral_cos hφ]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr' : r ∈ Icc 0 π := by simpa [uIcc_of_le pi_pos.le] using hr
    rw [mul_assoc (φ _), haarRealPartDensity_one_sub_cos_mul_sin hr'.1 hr'.2]
    have := pi_pos
    field_simp
    ring
  have hz : ∀ s : ℝ, partitionFn s = haarCharacterMean s := by
    intro s
    have h := hlaw (fun t => Real.exp (s * (1 - t))) (by fun_prop)
    simp only [sub_sub_cancel] at h
    unfold partitionFn haarCharacterMean haarLaplace
    rw [h, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  refine ⟨hlaw, hz, fun s => ?_⟩
  unfold logPartitionGap haarGap
  rw [hz]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
