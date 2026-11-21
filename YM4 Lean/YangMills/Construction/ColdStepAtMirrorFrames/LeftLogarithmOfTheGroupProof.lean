import YangMills.Construction.ColdStepAtMirrorFrames.LeftLogarithmOfTheGroup
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages NormedSpace
namespace YangMills.Construction.ColdStepAtMirrorFrames.QuaternionLog
def imPartLinear : ℍ[ℝ] →ₗ[ℝ] imaginaryQuaternions where
  toFun q := ⟨q.im, by change (q.im).re = 0; simp⟩
  map_add' p q := Subtype.ext (by ext <;> simp)
  map_smul' c q := Subtype.ext (by ext <;> simp)
def imPart : ℍ[ℝ] →L[ℝ] imaginaryQuaternions :=
  ⟨imPartLinear, imPartLinear.continuous_of_finiteDimensional⟩
theorem imPart_apply_coe (q : ℍ[ℝ]) : ((imPart q : imaginaryQuaternions) : ℍ[ℝ]) = q.im := rfl
theorem imPart_coe (z : imaginaryQuaternions) : imPart (z : ℍ[ℝ]) = z := by
  apply Subtype.ext
  have hz : (z : ℍ[ℝ]).re = 0 := z.2
  rw [imPart_apply_coe]
  ext <;> simp [hz]
theorem imPart_one : imPart (1 : ℍ[ℝ]) = 0 := by
  apply Subtype.ext
  rw [imPart_apply_coe]
  ext <;> simp
theorem norm_exp_coe (w : imaginaryQuaternions) : ‖exp (w : ℍ[ℝ])‖ = 1 := by
  have hw : (w : ℍ[ℝ]).re = 0 := w.2
  rw [Quaternion.norm_exp, hw]
  simp
theorem contDiff_quaternion_exp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (exp : ℍ[ℝ] → ℍ[ℝ]) :=
  contDiff_iff_contDiffAt.2 fun x => (exp_analytic (𝕂 := ℝ) x).contDiffAt
theorem eq_of_imPart_eq {p q : ℍ[ℝ]} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hi : imPart p = imPart q)
    (hpr : 0 < p.re) (hqr : 0 < q.re) : p = q := by
  have hi' : p.im = q.im := by
    have := congrArg (fun z : imaginaryQuaternions => (z : ℍ[ℝ])) hi
    simpa [imPart_apply_coe] using this
  have h1 : p.imI = q.imI := by simpa using congrArg (fun r : ℍ[ℝ] => r.imI) hi'
  have h2 : p.imJ = q.imJ := by simpa using congrArg (fun r : ℍ[ℝ] => r.imJ) hi'
  have h3 : p.imK = q.imK := by simpa using congrArg (fun r : ℍ[ℝ] => r.imK) hi'
  have hn : ∀ r : ℍ[ℝ], ‖r‖ = 1 → r.re ^ 2 + r.imI ^ 2 + r.imJ ^ 2 + r.imK ^ 2 = 1 := by
    intro r hr
    have h := Quaternion.normSq_eq_norm_mul_self r
    rw [hr, Quaternion.normSq_def'] at h
    linarith
  have hp' := hn p hp
  have hq' := hn q hq
  rw [h1, h2, h3] at hp'
  have hre : p.re = q.re := by nlinarith
  ext <;> assumption
def imExp (z : imaginaryQuaternions) : imaginaryQuaternions := imPart (exp (z : ℍ[ℝ]))
theorem imExp_zero : imExp 0 = 0 := by simp [imExp, imPart_one]
theorem contDiff_imExp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) imExp :=
  imPart.contDiff.comp (contDiff_quaternion_exp.comp imaginaryQuaternions.subtypeL.contDiff)
theorem hasFDerivAt_imExp :
    HasFDerivAt imExp ((ContinuousLinearEquiv.refl ℝ imaginaryQuaternions :
      imaginaryQuaternions ≃L[ℝ] imaginaryQuaternions) :
        imaginaryQuaternions →L[ℝ] imaginaryQuaternions) 0 := by
  have h1 : HasFDerivAt (exp : ℍ[ℝ] → ℍ[ℝ]) (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ])
      ((imaginaryQuaternions.subtypeL : imaginaryQuaternions →L[ℝ] ℍ[ℝ]) 0) := by
    simpa using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ℍ[ℝ])).hasFDerivAt
  have h2 := imPart.hasFDerivAt.comp (0 : imaginaryQuaternions)
    (h1.comp (0 : imaginaryQuaternions) imaginaryQuaternions.subtypeL.hasFDerivAt)
  have h3 : HasFDerivAt imExp
      (imPart.comp ((1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ]).comp imaginaryQuaternions.subtypeL)) 0 := h2
  refine h3.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun z => ?_
  change imPart (z : ℍ[ℝ]) = z
  exact imPart_coe z
def imLog : imaginaryQuaternions → imaginaryQuaternions :=
  (contDiff_imExp.contDiffAt (x := (0 : imaginaryQuaternions))).localInverse hasFDerivAt_imExp
    (by simp)
theorem contDiffAt_imLog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) imLog 0 := by
  have := (contDiff_imExp.contDiffAt (x := (0 : imaginaryQuaternions))).to_localInverse
    hasFDerivAt_imExp (by simp)
  rwa [imExp_zero] at this
theorem imLog_zero : imLog 0 = 0 := by
  have := (contDiff_imExp.contDiffAt (x := (0 : imaginaryQuaternions))).localInverse_apply_image
    hasFDerivAt_imExp (by simp)
  rwa [imExp_zero] at this
theorem eventually_imExp_imLog :
    ∀ᶠ y in 𝓝 (0 : imaginaryQuaternions), imExp (imLog y) = y := by
  have := ((contDiff_imExp.contDiffAt (x := (0 : imaginaryQuaternions))).hasStrictFDerivAt'
    hasFDerivAt_imExp (by simp)).eventually_right_inverse
  rwa [imExp_zero] at this
def twistedIm (p : imaginaryQuaternions × imaginaryQuaternions) : imaginaryQuaternions :=
  imPart (exp ((p.1 + p.2 : imaginaryQuaternions) : ℍ[ℝ]) * exp (-(p.1 : ℍ[ℝ])))
theorem exp_neg_eq_inv (x : ℍ[ℝ]) : exp (-x) = (exp x)⁻¹ :=
  exp_neg_of_mem_ball (𝕂 := ℝ) (by rw [expSeries_radius_eq_top]; simp)
theorem exp_coe_mul_exp_neg (v : imaginaryQuaternions) :
    exp (v : ℍ[ℝ]) * exp (-(v : ℍ[ℝ])) = 1 := by
  have h0 : exp (v : ℍ[ℝ]) ≠ 0 := by
    intro h
    have := norm_exp_coe v
    simp [h] at this
  rw [exp_neg_eq_inv, mul_inv_cancel₀ h0]
theorem twistedIm_zero (v : imaginaryQuaternions) : twistedIm (v, 0) = 0 := by
  simp [twistedIm, exp_coe_mul_exp_neg, imPart_one]
theorem contDiff_twistedIm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) twistedIm := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun p : imaginaryQuaternions × imaginaryQuaternions =>
        ((p.1 + p.2 : imaginaryQuaternions) : ℍ[ℝ]) :=
    imaginaryQuaternions.subtypeL.contDiff.comp (contDiff_fst.add contDiff_snd)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun p : imaginaryQuaternions × imaginaryQuaternions => -(p.1 : ℍ[ℝ]) :=
    (imaginaryQuaternions.subtypeL.contDiff.comp contDiff_fst).neg
  exact imPart.contDiff.comp ((contDiff_quaternion_exp.comp h1).mul (contDiff_quaternion_exp.comp h2))
def leftLog (p : imaginaryQuaternions × imaginaryQuaternions) : imaginaryQuaternions :=
  imLog (twistedIm p)
theorem leftLog_zero (v : imaginaryQuaternions) : leftLog (v, 0) = 0 := by
  simp [leftLog, twistedIm_zero, imLog_zero]
theorem contDiffAt_leftLog (v : imaginaryQuaternions) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) leftLog (v, 0) := by
  have h : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) imLog (twistedIm (v, 0)) := by
    rw [twistedIm_zero]
    exact contDiffAt_imLog
  exact h.comp (v, 0) contDiff_twistedIm.contDiffAt
theorem eventually_expUnit_add (v : imaginaryQuaternions) :
    ∀ᶠ z in 𝓝 (0 : imaginaryQuaternions),
      expUnit (v + z) = expUnit (leftLog (v, z)) * expUnit v := by
  have hpair : Filter.Tendsto (fun z : imaginaryQuaternions => (v, z)) (𝓝 0) (𝓝 (v, 0)) :=
    (Continuous.prodMk continuous_const continuous_id).tendsto' _ _ rfl
  have hin : Filter.Tendsto (fun z : imaginaryQuaternions => twistedIm (v, z)) (𝓝 0) (𝓝 0) := by
    have := (contDiff_twistedIm.continuous.tendsto (v, 0)).comp hpair
    simpa [twistedIm_zero, Function.comp_def] using this
  have hth : Filter.Tendsto (fun z : imaginaryQuaternions => leftLog (v, z)) (𝓝 0) (𝓝 0) := by
    have := ((contDiffAt_leftLog v).continuousAt.tendsto).comp hpair
    simpa [leftLog_zero, Function.comp_def] using this
  have hq : Filter.Tendsto (fun z : imaginaryQuaternions =>
      exp ((v + z : imaginaryQuaternions) : ℍ[ℝ]) * exp (-(v : ℍ[ℝ]))) (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun z : imaginaryQuaternions =>
        exp ((v + z : imaginaryQuaternions) : ℍ[ℝ]) * exp (-(v : ℍ[ℝ])) :=
      ((contDiff_quaternion_exp.continuous.comp (imaginaryQuaternions.subtypeL.continuous.comp
        (continuous_const.add continuous_id))).mul continuous_const)
    have := hc.tendsto 0
    simpa [exp_coe_mul_exp_neg] using this
  have he : Filter.Tendsto (fun z : imaginaryQuaternions =>
      exp ((leftLog (v, z) : imaginaryQuaternions) : ℍ[ℝ])) (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun y : imaginaryQuaternions => exp ((y : imaginaryQuaternions) : ℍ[ℝ]) :=
      contDiff_quaternion_exp.continuous.comp imaginaryQuaternions.subtypeL.continuous
    have := (hc.tendsto 0).comp hth
    simpa [Function.comp_def] using this
  have hre : Continuous fun q : ℍ[ℝ] => q.re := Quaternion.continuous_re
  have h1 : ∀ᶠ z in 𝓝 (0 : imaginaryQuaternions),
      0 < (exp ((v + z : imaginaryQuaternions) : ℍ[ℝ]) * exp (-(v : ℍ[ℝ]))).re := by
    have := (hre.tendsto 1).comp hq
    exact this.eventually (lt_mem_nhds (by simp))
  have h2 : ∀ᶠ z in 𝓝 (0 : imaginaryQuaternions),
      0 < (exp ((leftLog (v, z) : imaginaryQuaternions) : ℍ[ℝ])).re := by
    have := (hre.tendsto 1).comp he
    exact this.eventually (lt_mem_nhds (by simp))
  have h3 : ∀ᶠ z in 𝓝 (0 : imaginaryQuaternions), imExp (leftLog (v, z)) = twistedIm (v, z) :=
    hin.eventually eventually_imExp_imLog
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  have hneg : ‖exp (-(v : ℍ[ℝ]))‖ = 1 := by
    have := norm_exp_coe (-v)
    simpa using this
  have hnq : ‖exp ((v + z : imaginaryQuaternions) : ℍ[ℝ]) * exp (-(v : ℍ[ℝ]))‖ = 1 := by
    rw [norm_mul, norm_exp_coe, hneg, one_mul]
  have hq' := eq_of_imPart_eq (norm_exp_coe (leftLog (v, z))) hnq hz3 hz2 hz1
  apply Subtype.ext
  change exp ((v + z : imaginaryQuaternions) : ℍ[ℝ]) =
    exp ((leftLog (v, z) : imaginaryQuaternions) : ℍ[ℝ]) * exp (v : ℍ[ℝ])
  rw [hq', mul_assoc]
  have : exp (-(v : ℍ[ℝ])) * exp (v : ℍ[ℝ]) = 1 := by
    have h0 : exp (v : ℍ[ℝ]) ≠ 0 := by
      intro h
      have := norm_exp_coe v
      simp [h] at this
    rw [exp_neg_eq_inv, inv_mul_cancel₀ h0]
  rw [this, mul_one]
theorem exists_bound_iteratedFDeriv_leftLog (j : ℕ) :
    ∃ C : ℝ, ∀ v : imaginaryQuaternions, ‖v‖ ≤ 1 → ‖iteratedFDeriv ℝ j leftLog (v, 0)‖ ≤ C := by
  have : ProperSpace imaginaryQuaternions := FiniteDimensional.proper_real imaginaryQuaternions
  have hK : IsCompact (Metric.closedBall (0 : imaginaryQuaternions) 1) := isCompact_closedBall _ _
  have hc : ContinuousOn (fun v : imaginaryQuaternions => ‖iteratedFDeriv ℝ j leftLog (v, 0)‖)
      (Metric.closedBall (0 : imaginaryQuaternions) 1) := by
    intro v _
    have h1 : ContDiffAt ℝ 0 (iteratedFDeriv ℝ j leftLog) (v, 0) :=
      (contDiffAt_leftLog v).iteratedFDeriv_right (m := 0) (i := j) (by
        simp only [zero_add]
        exact_mod_cast le_top)
    have h4 : ContDiffAt ℝ 0 (fun v : imaginaryQuaternions => iteratedFDeriv ℝ j leftLog (v, 0)) v :=
      ContDiffAt.comp v h1 (contDiff_id.prodMk contDiff_const).contDiffAt
    have h5 : ContinuousAt
        (fun v : imaginaryQuaternions => ‖iteratedFDeriv ℝ j leftLog (v, 0)‖) v :=
      ContinuousAt.comp
        (f := fun v : imaginaryQuaternions => iteratedFDeriv ℝ j leftLog (v, 0))
        (g := fun A => ‖A‖)
        (continuous_norm (E := ContinuousMultilinearMap ℝ
          (fun _ : Fin j => imaginaryQuaternions × imaginaryQuaternions)
          imaginaryQuaternions)).continuousAt
        h4.continuousAt
    exact h5.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨C, fun v hv => (le_abs_self _).trans (by simpa using hC v (by simpa using hv))⟩
theorem leftLogarithmExists_holds : LeftLogarithmExists := by
  obtain ⟨C0, h0⟩ := exists_bound_iteratedFDeriv_leftLog 0
  obtain ⟨C1, h1⟩ := exists_bound_iteratedFDeriv_leftLog 1
  obtain ⟨C2, h2⟩ := exists_bound_iteratedFDeriv_leftLog 2
  obtain ⟨C3, h3⟩ := exists_bound_iteratedFDeriv_leftLog 3
  refine ⟨leftLog, |C0| + |C1| + |C2| + |C3| + 1, by positivity, contDiffAt_leftLog, leftLog_zero,
    eventually_expUnit_add, ?_⟩
  intro v j hv hj
  have a0 := abs_nonneg C0
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg C2
  have a3 := abs_nonneg C3
  interval_cases j
  · linarith [h0 v hv, le_abs_self C0]
  · linarith [h1 v hv, le_abs_self C1]
  · linarith [h2 v hv, le_abs_self C2]
  · linarith [h3 v hv, le_abs_self C3]
end YangMills.Construction.ColdStepAtMirrorFrames.QuaternionLog
end
