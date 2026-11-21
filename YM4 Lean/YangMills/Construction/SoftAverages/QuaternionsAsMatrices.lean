import YangMills.Construction.SoftAverages.ModelsOfAStep
import Mathlib
set_option autoImplicit false
open scoped Quaternion Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace SoftAverages
theorem quaternionToMatrix_apply (q : ℍ[ℝ]) :
    quaternionToMatrix q = !![(q.re : ℂ) + Complex.I * q.imI, (q.imJ : ℂ) + Complex.I * q.imK;
      -(q.imJ : ℂ) + Complex.I * q.imK, (q.re : ℂ) - Complex.I * q.imI] := rfl
theorem quaternionToMatrix_one : quaternionToMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionToMatrix]
theorem quaternionToMatrix_add (p q : ℍ[ℝ]) :
    quaternionToMatrix (p + q) = quaternionToMatrix p + quaternionToMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionToMatrix] <;> ring
theorem quaternionToMatrix_mul (p q : ℍ[ℝ]) :
    quaternionToMatrix (p * q) = quaternionToMatrix p * quaternionToMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionToMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring
def quaternionToMatrixRingHom : ℍ[ℝ] →+* Matrices.ComplexMatrix2 where
  toFun := quaternionToMatrix
  map_one' := quaternionToMatrix_one
  map_mul' := quaternionToMatrix_mul
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quaternionToMatrix]
  map_add' := quaternionToMatrix_add
theorem continuous_quaternionToMatrix : Continuous quaternionToMatrix := by
  have hre : Continuous fun q : ℍ[ℝ] => (q.re : ℂ) := Complex.continuous_ofReal.comp Quaternion.continuous_re
  have hi : Continuous fun q : ℍ[ℝ] => (q.imI : ℂ) :=
    Complex.continuous_ofReal.comp Quaternion.continuous_imI
  have hj : Continuous fun q : ℍ[ℝ] => (q.imJ : ℂ) :=
    Complex.continuous_ofReal.comp Quaternion.continuous_imJ
  have hk : Continuous fun q : ℍ[ℝ] => (q.imK : ℂ) :=
    Complex.continuous_ofReal.comp Quaternion.continuous_imK
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [quaternionToMatrix]
  · exact hre.add (continuous_const.mul hi)
  · exact hj.add (continuous_const.mul hk)
  · exact hj.neg.add (continuous_const.mul hk)
  · exact hre.sub (continuous_const.mul hi)
def colorMatrix (v : Fin 3 → ℂ) : Matrices.ComplexMatrix2 :=
  !![Complex.I * v 0, v 1 + Complex.I * v 2; -v 1 + Complex.I * v 2, -(Complex.I * v 0)]
def colorExp (v : Fin 3 → ℂ) : Matrices.ComplexMatrix2 :=
  Matrices.ComplexMatrix2.matExp (colorMatrix v)
def pureQuaternion (w : Fin 3 → ℝ) : ℍ[ℝ] := ⟨0, w 0, w 1, w 2⟩
theorem colorMatrix_ofReal (w : Fin 3 → ℝ) :
    colorMatrix (fun i => (w i : ℂ)) = quaternionToMatrix (pureQuaternion w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [colorMatrix, quaternionToMatrix, pureQuaternion]
theorem colorExp_ofReal (w : Fin 3 → ℝ) :
    colorExp (fun i => (w i : ℂ)) = quaternionToMatrix (NormedSpace.exp (pureQuaternion w)) := by
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (𝔸 := ℍ[ℝ]) (𝔹 := Matrices.ComplexMatrix2)
    quaternionToMatrixRingHom continuous_quaternionToMatrix (pureQuaternion w)
    (by rw [NormedSpace.expSeries_radius_eq_top]; simp)
  change quaternionToMatrix (NormedSpace.exp (pureQuaternion w)) =
    NormedSpace.exp (quaternionToMatrix (pureQuaternion w)) at h
  rw [h, ← colorMatrix_ofReal]
  rfl
end SoftAverages
end YangMills.Construction
end
