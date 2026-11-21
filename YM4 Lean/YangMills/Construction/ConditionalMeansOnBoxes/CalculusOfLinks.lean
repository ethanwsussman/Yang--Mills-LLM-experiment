import YangMills.Construction.ConditionalMeansOnBoxes.TreeGaugeAndSmearedCurvature
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.ConditionalMeansOnBoxes
open Matrices
theorem specialUnitary_entries (V : ComplexMatrix2.specialUnitary) :
    (V : ComplexMatrix2) 1 0 = -(starRingEnd ℂ) ((V : ComplexMatrix2) 0 1) ∧
      (V : ComplexMatrix2) 1 1 = (starRingEnd ℂ) ((V : ComplexMatrix2) 0 0) ∧
      ((V : ComplexMatrix2) 0 0).re ^ 2 + ((V : ComplexMatrix2) 0 0).im ^ 2 +
        ((V : ComplexMatrix2) 0 1).re ^ 2 + ((V : ComplexMatrix2) 0 1).im ^ 2 = 1 := by
  have hmem := (Matrix.mem_specialUnitaryGroup_iff.mp V.2)
  have hunit : (V : ComplexMatrix2) * star (V : ComplexMatrix2) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hmem.1
  have hdet : ((V : ComplexMatrix2)).det = 1 := hmem.2
  have hadj : Matrix.adjugate (V : ComplexMatrix2) * (V : ComplexMatrix2) = 1 := by
    rw [Matrix.adjugate_mul, hdet, one_smul]
  have hstar : star (V : ComplexMatrix2) = Matrix.adjugate (V : ComplexMatrix2) := by
    calc star (V : ComplexMatrix2)
        = (Matrix.adjugate (V : ComplexMatrix2) * (V : ComplexMatrix2)) * star (V : ComplexMatrix2) := by
          rw [hadj, one_mul]
      _ = Matrix.adjugate (V : ComplexMatrix2) := by rw [mul_assoc, hunit, mul_one]
  have h01 := congrFun (congrFun hstar 0) 1
  have h00 := congrFun (congrFun hstar 0) 0
  rw [Matrix.adjugate_fin_two] at h01 h00
  simp [Matrix.star_apply] at h01 h00
  have hrow := congrFun (congrFun hunit 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at hrow
  refine ⟨?_, h00.symm, ?_⟩
  · have hc := congrArg (starRingEnd ℂ) h01
    simp at hc
    rw [← hc]
  · have hre := congrArg Complex.re hrow
    simp at hre
    nlinarith [hre]
theorem toQuaternion_mul (V W : ComplexMatrix2.specialUnitary) :
    toQuaternion (V * W) = toQuaternion V * toQuaternion W := by
  obtain ⟨hW10, hW11, -⟩ := specialUnitary_entries W
  have e00 : ((V * W : ComplexMatrix2.specialUnitary) : ComplexMatrix2) 0 0 =
      (V : ComplexMatrix2) 0 0 * (W : ComplexMatrix2) 0 0 +
        (V : ComplexMatrix2) 0 1 * (W : ComplexMatrix2) 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : ((V * W : ComplexMatrix2.specialUnitary) : ComplexMatrix2) 0 1 =
      (V : ComplexMatrix2) 0 0 * (W : ComplexMatrix2) 0 1 +
        (V : ComplexMatrix2) 0 1 * (W : ComplexMatrix2) 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hW10] at e00
  rw [hW11] at e01
  ext
  · rw [Quaternion.re_mul]
    simp only [toQuaternion, e00]
    simp
    ring
  · rw [Quaternion.imI_mul]
    simp only [toQuaternion, e00]
    simp
    ring
  · rw [Quaternion.imJ_mul]
    simp only [toQuaternion, e01]
    simp
    ring
  · rw [Quaternion.imK_mul]
    simp only [toQuaternion, e01]
    simp
    ring
theorem norm_toQuaternion (V : ComplexMatrix2.specialUnitary) : ‖toQuaternion V‖ = 1 := by
  obtain ⟨-, -, hsum⟩ := specialUnitary_entries V
  have hsq : Quaternion.normSq (toQuaternion V) = 1 := by
    rw [Quaternion.normSq_def']
    simpa [toQuaternion] using hsum
  have hmul : ‖toQuaternion V‖ * ‖toQuaternion V‖ = 1 := by
    rw [← Quaternion.normSq_eq_norm_mul_self, hsq]
  nlinarith [norm_nonneg (toQuaternion V)]
theorem toQuaternion_one : toQuaternion (1 : ComplexMatrix2.specialUnitary) = 1 := by
  ext <;> simp [toQuaternion]
theorem toQuaternion_mul_star (V : ComplexMatrix2.specialUnitary) :
    toQuaternion V * star (toQuaternion V) = 1 := by
  rw [Quaternion.self_mul_star]
  have hn := norm_toQuaternion V
  rw [Quaternion.normSq_eq_norm_mul_self, hn]
  simp
theorem toQuaternion_inv (V : ComplexMatrix2.specialUnitary) :
    toQuaternion V⁻¹ = star (toQuaternion V) := by
  have hleft : toQuaternion V⁻¹ * toQuaternion V = 1 := by
    rw [← toQuaternion_mul, inv_mul_cancel, toQuaternion_one]
  calc toQuaternion V⁻¹ = toQuaternion V⁻¹ * (toQuaternion V * star (toQuaternion V)) := by
        rw [toQuaternion_mul_star, mul_one]
    _ = star (toQuaternion V) := by rw [← mul_assoc, hleft, one_mul]
theorem re_fullTrace_eq_two_mul_re (V : ComplexMatrix2.specialUnitary) :
    (ComplexMatrix2.fullTrace (V : ComplexMatrix2)).re = 2 * (toQuaternion V).re := by
  obtain ⟨-, hV11, -⟩ := specialUnitary_entries V
  simp [ComplexMatrix2.fullTrace, Matrix.trace, Fin.sum_univ_two, hV11, toQuaternion]
  ring
def quaternionI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
def quaternionJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
def quaternionK : ℍ[ℝ] := ⟨0, 0, 0, 1⟩
theorem continuous_toQuaternion : Continuous toQuaternion := by
  have c00 : Continuous fun V : ComplexMatrix2.specialUnitary => (V : ComplexMatrix2) 0 0 :=
    (continuous_subtype_val).matrix_elem 0 0
  have c01 : Continuous fun V : ComplexMatrix2.specialUnitary => (V : ComplexMatrix2) 0 1 :=
    (continuous_subtype_val).matrix_elem 0 1
  have hform : toQuaternion = fun V : ComplexMatrix2.specialUnitary =>
      (((V : ComplexMatrix2) 0 0).re : ℍ[ℝ]) + (((V : ComplexMatrix2) 0 0).im : ℍ[ℝ]) * quaternionI +
        (((V : ComplexMatrix2) 0 1).re : ℍ[ℝ]) * quaternionJ +
          (((V : ComplexMatrix2) 0 1).im : ℍ[ℝ]) * quaternionK := by
    funext V
    have i0 : quaternionI.re = 0 := rfl
    have i1 : quaternionI.imI = 1 := rfl
    have i2 : quaternionI.imJ = 0 := rfl
    have i3 : quaternionI.imK = 0 := rfl
    have j0 : quaternionJ.re = 0 := rfl
    have j1 : quaternionJ.imI = 0 := rfl
    have j2 : quaternionJ.imJ = 1 := rfl
    have j3 : quaternionJ.imK = 0 := rfl
    have k0 : quaternionK.re = 0 := rfl
    have k1 : quaternionK.imI = 0 := rfl
    have k2 : quaternionK.imJ = 0 := rfl
    have k3 : quaternionK.imK = 1 := rfl
    ext <;> simp [toQuaternion, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, i0, i1, i2, i3, j0, j1, j2, j3, k0, k1, k2, k3]
  rw [hform]
  have hcoe := Quaternion.continuous_coe
  have e1 := hcoe.comp (Complex.continuous_re.comp c00)
  have e2 := hcoe.comp (Complex.continuous_im.comp c00)
  have e3 := hcoe.comp (Complex.continuous_re.comp c01)
  have e4 := hcoe.comp (Complex.continuous_im.comp c01)
  exact ((e1.add (e2.mul continuous_const)).add (e3.mul continuous_const)).add
    (e4.mul continuous_const)
theorem exists_toQuaternion_eq_of_norm_eq_one (q : ℍ[ℝ]) (hq : ‖q‖ = 1) :
    ∃ V : ComplexMatrix2.specialUnitary, toQuaternion V = q := by
  have hsum : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1 := by
    have hsq : Quaternion.normSq q = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, hq]; simp
    rwa [Quaternion.normSq_def'] at hsq
  set α : ℂ := ⟨q.re, q.imI⟩ with hα
  set β : ℂ := ⟨q.imJ, q.imK⟩ with hβ
  let M : ComplexMatrix2 := !![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α]
  have hM : M ∈ ComplexMatrix2.specialUnitary := by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
        apply Complex.ext <;> simp [hα, hβ] <;> nlinarith [hsum]
    · simp only [M, Matrix.det_fin_two_of]
      apply Complex.ext <;> simp [hα, hβ] <;> nlinarith [hsum]
  refine ⟨⟨M, hM⟩, ?_⟩
  ext <;> simp [toQuaternion, M, hα, hβ]
end YangMills.Construction.ConditionalMeansOnBoxes
end
