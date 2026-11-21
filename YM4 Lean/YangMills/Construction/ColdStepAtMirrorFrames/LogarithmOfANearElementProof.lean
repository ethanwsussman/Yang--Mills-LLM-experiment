import YangMills.Construction.ColdStepAtMirrorFrames.LogarithmOfANearElement
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ColdStepAtMirrorFrames
open BlockAverages BlockOffsets
theorem logNearOne_holds : LogNearOne := by
  intro g hg
  set q : ℍ[ℝ] := (g : ℍ[ℝ]) with hq
  have hn : ‖q‖ = 1 := _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.norm_coe_unitQuaternion g
  have hsq : q.re ^ 2 + ‖q.im‖ ^ 2 = 1 := by
    have h1 := Quaternion.normSq_eq_norm_mul_self q
    have h2 : Quaternion.normSq q = q.re * q.re + Quaternion.normSq q.im := by
      rw [Quaternion.normSq_def', Quaternion.normSq_def']
      simp
      ring
    rw [Quaternion.normSq_eq_norm_mul_self q.im, hn] at *
    nlinarith
  have hdist : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g ^ 2 = 2 - 2 * q.re := by
    unfold _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne
    have e1 : ‖q - 1‖ ^ 2 = Quaternion.normSq (q - 1) := by
      rw [Quaternion.normSq_eq_norm_mul_self, sq]
    have e2 : Quaternion.normSq q = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, hn]; norm_num
    have e3 : Quaternion.normSq (q - 1) = Quaternion.normSq q - 2 * q.re + 1 := by
      simp only [Quaternion.normSq_def', Quaternion.re_sub, Quaternion.imI_sub, Quaternion.imJ_sub,
        Quaternion.imK_sub, Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one,
        Quaternion.imK_one]
      ring
    show ‖q - 1‖ ^ 2 = _
    rw [e1, e3, e2]
    ring
  have hd0 : 0 ≤ _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g := distFromOne_nonneg g
  have hre : 0 < q.re := by nlinarith
  set s := ‖q.im‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg _
  have hs1 : s ≤ 1 := by nlinarith
  have hsd : s ≤ _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g := by
    have : s ^ 2 ≤ _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g ^ 2 := by nlinarith
    exact abs_le_of_sq_le_sq' this hd0 |>.2
  by_cases h0 : s = 0
  · refine ⟨0, ?_, by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd0⟩
    have hre1 : q.re = 1 := by nlinarith
    have him : q.im = 0 := by simpa [hs] using h0
    apply Subtype.ext
    show NormedSpace.exp (((0 : imaginaryQuaternions)) : ℍ[ℝ]) = q
    have : q = 1 := by
      rw [← Quaternion.re_add_im q, hre1, him]
      simp
    rw [this]
    simp
  · have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
    set θ := Real.arcsin s with hθ
    have hθ0 : 0 ≤ θ := Real.arcsin_nonneg.mpr hs0
    have hθ2 : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two s
    have hsin : Real.sin θ = s := Real.sin_arcsin (by linarith) hs1
    have hcos : Real.cos θ = q.re := by
      rw [hθ, Real.cos_arcsin]
      have : 1 - s ^ 2 = q.re ^ 2 := by linarith
      rw [this, Real.sqrt_sq hre.le]
    have hθp : 0 < θ := by
      rcases hθ0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hsin; simp at hsin; exact absurd hsin.symm h0
    let A : imaginaryQuaternions := ⟨(θ / s) • q.im, by
      show ((θ / s) • q.im).re = 0
      simp⟩
    have hAn : ‖(A : ℍ[ℝ])‖ = θ := by
      show ‖(θ / s) • q.im‖ = θ
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← hs]
      field_simp
    refine ⟨A, ?_, ?_⟩
    · apply Subtype.ext
      show NormedSpace.exp (A : ℍ[ℝ]) = q
      rw [exp_imaginary_eq A, hAn, hcos, hsin]
      show (q.re : ℍ[ℝ]) + (s / θ) • ((θ / s) • q.im) = q
      rw [smul_smul]
      have : s / θ * (θ / s) = 1 := by field_simp
      rw [this, one_smul, Quaternion.re_add_im]
    · have hj := Real.mul_le_sin hθ0 hθ2
      rw [hsin] at hj
      show ‖(A : ℍ[ℝ])‖ ≤ _
      rw [hAn]
      have hpi := Real.pi_le_four
      have : θ ≤ Real.pi / 2 * s := by
        have := mul_le_mul_of_nonneg_left hj (by positivity : 0 ≤ Real.pi / 2)
        have e : Real.pi / 2 * (2 / Real.pi * θ) = θ := by field_simp
        linarith
      nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames
end
