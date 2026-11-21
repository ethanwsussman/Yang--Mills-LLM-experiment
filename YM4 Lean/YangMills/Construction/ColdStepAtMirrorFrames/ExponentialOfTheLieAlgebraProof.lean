import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import YangMills.Construction.ColdStepAtMirrorFrames.ExponentialOfTheLieAlgebra
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.QuaternionExp
theorem norm_coe_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem norm_exp_smul_imaginary (s : ℝ) (v : imaginaryQuaternions) :
    ‖NormedSpace.exp (s • (v : ℍ[ℝ]))‖ = 1 := by
  have := norm_coe_unitQuaternion (expUnit (s • v))
  simpa [expUnit] using this
theorem expUnitLipschitzInjective_holds : ExpUnitLipschitzInjective := by
  refine ⟨fun v w => ?_, fun v w hv hw h => ?_⟩
  · let +nondep : NormedAlgebra ℚ ℍ[ℝ] := .restrictScalars ℚ ℝ ℍ[ℝ]
    set u : ℝ → ℍ[ℝ] := fun s => NormedSpace.exp (s • (v : ℍ[ℝ])) * NormedSpace.exp ((1 - s) • (w : ℍ[ℝ])) with hu
    have hd : ∀ s : ℝ, HasDerivAt u (NormedSpace.exp (s • (v : ℍ[ℝ])) * ((v : ℍ[ℝ]) - (w : ℍ[ℝ])) *
        NormedSpace.exp ((1 - s) • (w : ℍ[ℝ]))) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (v : ℍ[ℝ])))
          (NormedSpace.exp (s • (v : ℍ[ℝ])) * (v : ℍ[ℝ])) s := hasDerivAt_exp_smul_const _ _
      have h3 : HasDerivAt (fun r : ℝ => NormedSpace.exp (r • (w : ℍ[ℝ])))
          ((w : ℍ[ℝ]) * NormedSpace.exp ((1 - s) • (w : ℍ[ℝ]))) (1 - s) := hasDerivAt_exp_smul_const' _ _
      have h4 : HasDerivAt (fun s : ℝ => 1 - s) (-1 : ℝ) s := by
        simpa using (hasDerivAt_id s).const_sub 1
      have h2 := h3.scomp s h4
      refine (h1.mul h2).congr_deriv ?_
      simp only [Function.comp_apply, neg_smul, one_smul]
      noncomm_ring
    have hb : ∀ s ∈ Set.Ico (0 : ℝ) 1, ‖deriv u s‖ ≤ ‖v - w‖ := by
      intro s _
      rw [(hd s).deriv, norm_mul, norm_mul, norm_exp_smul_imaginary, norm_exp_smul_imaginary, one_mul, mul_one]
      rfl
    have hm := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := u) (f' := deriv u)
      (fun s _ => (hd s).hasDerivWithinAt.congr_deriv (hd s).deriv.symm) hb
    have e0 : u 0 = NormedSpace.exp (w : ℍ[ℝ]) := by simp [hu]
    have e1 : u 1 = NormedSpace.exp (v : ℍ[ℝ]) := by simp [hu]
    rw [e0, e1] at hm
    exact hm
  · have hc := congrArg (fun g : UnitQuaternion => (g : ℍ[ℝ])) h
    have hv0 : (v : ℍ[ℝ]).re = 0 := v.2
    have hw0 : (w : ℍ[ℝ]).re = 0 := w.2
    change NormedSpace.exp (v : ℍ[ℝ]) = NormedSpace.exp (w : ℍ[ℝ]) at hc
    rw [Quaternion.exp_of_re_eq_zero _ hv0, Quaternion.exp_of_re_eq_zero _ hw0] at hc
    have hre := congrArg QuaternionAlgebra.re hc
    simp only [Quaternion.re_add, Quaternion.re_coe, Quaternion.re_smul, hv0, hw0, smul_zero,
      add_zero] at hre
    have hvn : ‖(v : ℍ[ℝ])‖ = ‖v‖ := rfl
    have hwn : ‖(w : ℍ[ℝ])‖ = ‖w‖ := rfl
    rw [hvn, hwn] at hre hc
    have hr : ‖v‖ = ‖w‖ := Real.injOn_cos ⟨norm_nonneg _, hv.le⟩ ⟨norm_nonneg _, hw.le⟩ hre
    by_cases h0 : ‖v‖ = 0
    · have e1 : v = 0 := norm_eq_zero.mp h0
      have e2 : w = 0 := norm_eq_zero.mp (hr ▸ h0)
      rw [e1, e2]
    · have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have hsin : 0 < Real.sin ‖v‖ := Real.sin_pos_of_pos_of_lt_pi hpos hv
      rw [← hr, hre] at hc
      have hc2 := add_left_cancel hc
      have hne : Real.sin ‖v‖ / ‖v‖ ≠ 0 := (div_pos hsin hpos).ne'
      exact Subtype.ext (smul_right_injective _ hne hc2)
end YangMills.Construction.QuaternionExp
end
