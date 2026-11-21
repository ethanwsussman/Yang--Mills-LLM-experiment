import YangMills.Construction.ColdChainAtEveryLevel.DensityUnderAChangeOfFramingProof
import YangMills.Construction.FormsOnATorus.GaugeActionDefs
import YangMills.Construction.HoleBesideASecondHole.ASegmentInTheGroupProof
import YangMills.Construction.RunningCouplingSlope.EnergyAtTheLeastFieldHasKernelsProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
open scoped Quaternion
namespace YangMills.Construction.GaugeCharts
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields
theorem re_coe_imaginary (w : imaginaryQuaternions) : (w : ℍ[ℝ]).re = 0 := w.2
theorem norm_sq_eq_sum_sq (q : ℍ[ℝ]) : ‖q‖ ^ 2 = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 := by
  rw [sq ‖q‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
theorem norm_sq_imaginary (w : imaginaryQuaternions) :
    ‖w‖ ^ 2 = (w : ℍ[ℝ]).imI ^ 2 + (w : ℍ[ℝ]).imJ ^ 2 + (w : ℍ[ℝ]).imK ^ 2 := by apply _root_.YangMills.SharedProofs.p1745 <;> assumption
theorem mem_unitary_of_norm_eq_one {q : ℍ[ℝ]} (hq : ‖q‖ = 1) : q ∈ unitary ℍ[ℝ] := by apply _root_.YangMills.Construction.GroupPaths.unitary_mem_of_norm_eq_one <;> assumption
theorem norm_unitQuaternion (g : UnitQuaternion) : ‖((g : UnitQuaternion) : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem mul_star_self_unitQuaternion (u : UnitQuaternion) : (u : ℍ[ℝ]) * star (u : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.BlockAverages.GaugeChangeDensity.unitQuaternion_mul_star <;> assumption
theorem coe_inv_unitQuaternion (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := rfl
theorem coe_imaginaryPart (q : ℍ[ℝ]) :
    ((imaginaryPart q : imaginaryQuaternions) : ℍ[ℝ]) = q - ((q.re : ℝ) : ℍ[ℝ]) := rfl
theorem norm_sq_eq_re_sq_add_imaginaryPart (q : ℍ[ℝ]) : ‖q‖ ^ 2 = q.re ^ 2 + ‖imaginaryPart q‖ ^ 2 := by
  rw [norm_sq_eq_sum_sq, norm_sq_imaginary, coe_imaginaryPart]
  simp
  ring
theorem imaginaryPart_coe_imaginary (y : imaginaryQuaternions) : imaginaryPart (y : ℍ[ℝ]) = y := by
  apply Subtype.ext
  rw [coe_imaginaryPart, re_coe_imaginary]
  simp
theorem imaginaryPart_coe_real (r : ℝ) : imaginaryPart ((r : ℝ) : ℍ[ℝ]) = 0 := by
  apply Subtype.ext
  rw [coe_imaginaryPart]
  simp
theorem imaginaryPart_hemispherePoint (y : imaginaryQuaternions) : imaginaryPart (hemispherePoint y) = y := by
  rw [hemispherePoint, map_add, imaginaryPart_coe_real, imaginaryPart_coe_imaginary, zero_add]
theorem re_hemispherePoint (y : imaginaryQuaternions) : (hemispherePoint y).re = Real.sqrt (1 - ‖y‖ ^ 2) := by
  simp [hemispherePoint, re_coe_imaginary]
theorem norm_hemispherePoint {y : imaginaryQuaternions} (hy : ‖y‖ ≤ 1) : ‖hemispherePoint y‖ = 1 := by
  have h := norm_sq_eq_re_sq_add_imaginaryPart (hemispherePoint y)
  rw [imaginaryPart_hemispherePoint, re_hemispherePoint, Real.sq_sqrt (by nlinarith [norm_nonneg y])] at h
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp (by rw [h]; ring)
theorem coe_hemisphereUnit {y : imaginaryQuaternions} (hy : ‖y‖ ≤ 1) :
    ((hemisphereUnit y : UnitQuaternion) : ℍ[ℝ]) = hemispherePoint y := by
  simp [hemisphereUnit, dif_pos (mem_unitary_of_norm_eq_one (norm_hemispherePoint hy))]
theorem hemispherePoint_imaginaryPart {q : ℍ[ℝ]} (hq : ‖q‖ = 1) (hr : 0 < q.re) :
    ‖imaginaryPart q‖ < 1 ∧ hemispherePoint (imaginaryPart q) = q := by
  have h := norm_sq_eq_re_sq_add_imaginaryPart q
  rw [hq] at h
  have hlt : ‖imaginaryPart q‖ < 1 := by
    have : ‖imaginaryPart q‖ ^ 2 < 1 := by nlinarith
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  refine ⟨hlt, ?_⟩
  have hs : Real.sqrt (1 - ‖imaginaryPart q‖ ^ 2) = q.re := by
    have : 1 - ‖imaginaryPart q‖ ^ 2 = q.re ^ 2 := by linarith
    rw [this, Real.sqrt_sq hr.le]
  rw [hemispherePoint, hs, coe_imaginaryPart]
  abel
theorem hemispherePoint_zero : hemispherePoint 0 = 1 := by
  simp [hemispherePoint]
theorem hemisphereUnit_zero : hemisphereUnit 0 = 1 := by
  apply Subtype.ext
  rw [coe_hemisphereUnit (by simp), hemispherePoint_zero]
  rfl
theorem continuous_hemispherePoint : Continuous hemispherePoint := by
  unfold hemispherePoint
  have h1 : Continuous fun y : imaginaryQuaternions => Real.sqrt (1 - ‖y‖ ^ 2) := by fun_prop
  exact (Quaternion.continuous_coe.comp h1).add continuous_subtype_val
theorem continuousOn_hemisphereUnit : ContinuousOn hemisphereUnit {y : imaginaryQuaternions | ‖y‖ ≤ 1} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun y : {y : imaginaryQuaternions | ‖y‖ ≤ 1} =>
      (⟨hemispherePoint y.1, mem_unitary_of_norm_eq_one (norm_hemispherePoint y.2)⟩ : UnitQuaternion) :=
    Continuous.subtype_mk (continuous_hemispherePoint.comp continuous_subtype_val) _
  convert hc using 1
  funext y
  apply Subtype.ext
  exact coe_hemisphereUnit y.2
theorem measurable_hemisphereUnit [MeasurableSpace imaginaryQuaternions] [BorelSpace imaginaryQuaternions] :
    Measurable hemisphereUnit := by
  have hs : MeasurableSet {y : imaginaryQuaternions | ‖y‖ ≤ 1} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  refine measurable_of_restrict_of_restrict_compl hs ?_ ?_
  · exact (continuousOn_iff_continuous_domRestrict.mp continuousOn_hemisphereUnit).measurable
  · have : ({y : imaginaryQuaternions | ‖y‖ ≤ 1}ᶜ).domRestrict hemisphereUnit = fun _ => 1 := by
      funext y
      have h1 : 1 < ‖y.1‖ := by simpa using y.2
      have h2 : hemispherePoint y.1 ∉ unitary ℍ[ℝ] := by
        intro hm
        have hn := norm_unitQuaternion ⟨hemispherePoint y.1, hm⟩
        have hs : Real.sqrt (1 - ‖y.1‖ ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by nlinarith)
        have hp : hemispherePoint y.1 = (y.1 : ℍ[ℝ]) := by
          rw [hemispherePoint, hs]
          simp
        simp only [hp] at hn
        have : ‖y.1‖ = 1 := hn
        linarith
      simp only [Set.domRestrict_apply, hemisphereUnit, dif_neg h2]
    rw [this]
    exact measurable_const
theorem hemisphereDensity_pos {y : imaginaryQuaternions} (hy : ‖y‖ < 1) : 0 < hemisphereDensity y :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by nlinarith [norm_nonneg y]))
theorem continuousOn_hemisphereDensity :
    ContinuousOn hemisphereDensity {y : imaginaryQuaternions | ‖y‖ < 1} := by
  unfold hemisphereDensity
  refine ContinuousOn.inv₀ (by fun_prop) fun y hy => (Real.sqrt_pos.mpr ?_).ne'
  have hy' : ‖y‖ < 1 := hy
  nlinarith [norm_nonneg y]
theorem hemisphereDensity_zero : hemisphereDensity 0 = 1 := by
  simp [hemisphereDensity]
theorem contDiffOn_hemispherePoint :
    ContDiffOn ℝ 1 hemispherePoint {y : imaginaryQuaternions | ‖y‖ < 1} := by
  have h1 : ContDiffOn ℝ 1 (fun y : imaginaryQuaternions => Real.sqrt (1 - ‖y‖ ^ 2))
      {y : imaginaryQuaternions | ‖y‖ < 1} := by
    refine ContDiffOn.sqrt ?_ ?_
    · exact (contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffOn
    · intro y hy
      have hy' : ‖y‖ < 1 := hy
      nlinarith [norm_nonneg y]
  have h2 : ContDiffOn ℝ 1 (fun y : imaginaryQuaternions => ((Real.sqrt (1 - ‖y‖ ^ 2) : ℝ) : ℍ[ℝ]))
      {y : imaginaryQuaternions | ‖y‖ < 1} :=
    (algebraMapCLM ℝ ℍ[ℝ]).contDiff.comp_contDiffOn h1
  exact h2.add imaginaryQuaternions.subtypeL.contDiff.contDiffOn
theorem hasFDerivAt_hemispherePoint_zero :
    HasFDerivAt hemispherePoint imaginaryQuaternions.subtypeL (0 : imaginaryQuaternions) := by
  have hn : HasFDerivAt (fun y : imaginaryQuaternions => ‖y‖ ^ 2) _ (0 : imaginaryQuaternions) :=
    (hasFDerivAt_id (0 : imaginaryQuaternions)).norm_sq
  have hs : HasFDerivAt (fun y : imaginaryQuaternions => Real.sqrt (1 - ‖y‖ ^ 2)) _ (0 : imaginaryQuaternions) :=
    ((hasFDerivAt_const (1 : ℝ) (0 : imaginaryQuaternions)).sub hn).sqrt (by simp)
  have hq := ((algebraMapCLM ℝ ℍ[ℝ]).hasFDerivAt.comp (0 : imaginaryQuaternions) hs).add
    imaginaryQuaternions.subtypeL.hasFDerivAt
  refine hq.congr_fderiv ?_
  ext y : 1
  simp
variable {ι κ : Type}
theorem gaugeAtEnd_mul (g h : ι → UnitQuaternion) (o : Option ι) :
    gaugeAtEnd (g * h) o = gaugeAtEnd g o * gaugeAtEnd h o := by
  cases o
  · simp [gaugeAtEnd]
  · rfl
theorem gaugeTransform_gaugeTransform (tl hd : κ → Option ι) (g h : ι → UnitQuaternion) (w : κ → UnitQuaternion) :
    gaugeTransform tl hd g (gaugeTransform tl hd h w) = gaugeTransform tl hd (g * h) w := by
  funext b
  simp only [gaugeTransform, gaugeAtEnd_mul, mul_inv_rev]
  group
theorem continuous_gaugeAtEnd (o : Option ι) : Continuous fun g : ι → UnitQuaternion => gaugeAtEnd g o := by
  cases o
  · exact continuous_const
  · exact continuous_apply _
end YangMills.Construction.GaugeCharts
end
