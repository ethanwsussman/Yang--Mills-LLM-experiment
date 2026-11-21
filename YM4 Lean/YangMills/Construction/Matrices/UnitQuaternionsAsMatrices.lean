import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace UnitQuaternions
def quatMatrix (q : ℍ[ℝ]) : Matrices.ComplexMatrix2 :=
  !![(q.re : ℂ) + q.imI * Complex.I, (q.imJ : ℂ) + q.imK * Complex.I;
     -(q.imJ : ℂ) + q.imK * Complex.I, (q.re : ℂ) - q.imI * Complex.I]
theorem quatMatrix_mul (p q : ℍ[ℝ]) :
    quatMatrix (p * q) = quatMatrix p * quatMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [quatMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
theorem quatMatrix_one : quatMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quatMatrix]
theorem quatMatrix_star (q : ℍ[ℝ]) :
    quatMatrix (star q) = star (quatMatrix q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [quatMatrix]
theorem det_quatMatrix (q : ℍ[ℝ]) :
    (quatMatrix q).det = ((Quaternion.normSq q : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two, Quaternion.normSq_def']
  apply Complex.ext <;> simp [quatMatrix, pow_two] <;> ring
theorem quatMatrix_mem_specialUnitary (u : BlockAverages.UnitQuaternion) :
    quatMatrix (u : ℍ[ℝ]) ∈ Matrices.ComplexMatrix2.specialUnitary := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  have hright : (u : ℍ[ℝ]) * star (u : ℍ[ℝ]) = 1 := (Unitary.mem_iff.mp u.2).2
  have hleft : star (u : ℍ[ℝ]) * (u : ℍ[ℝ]) = 1 := (Unitary.mem_iff.mp u.2).1
  refine ⟨?_, ?_⟩
  · rw [← quatMatrix_star, ← quatMatrix_mul, hright, quatMatrix_one]
  · rw [det_quatMatrix]
    rw [Quaternion.star_mul_self] at hleft
    have := congrArg (fun z : ℍ[ℝ] => z.re) hleft
    simp only [Quaternion.re_coe, Quaternion.re_one] at this
    rw [this]
    simp
def toSpecialUnitaryHom : BlockAverages.UnitQuaternion →* Matrices.ComplexMatrix2.specialUnitary where
  toFun u := ⟨quatMatrix (u : ℍ[ℝ]), quatMatrix_mem_specialUnitary u⟩
  map_one' := Subtype.ext quatMatrix_one
  map_mul' _ _ := Subtype.ext (quatMatrix_mul _ _)
theorem mem_unitary_of_normSq_eq_one (q : ℍ[ℝ]) (h : Quaternion.normSq q = 1) : q ∈ unitary ℍ[ℝ] :=
  Unitary.mem_iff.mpr ⟨by rw [Quaternion.star_mul_self, h]; simp, by rw [Quaternion.self_mul_star, h]; simp⟩
theorem toSpecialUnitaryHom_surjective : Function.Surjective toSpecialUnitaryHom := by
  rintro ⟨A, hA⟩
  have hD : A.det = 1 := (Matrix.mem_specialUnitaryGroup_iff.1 hA).2
  obtain ⟨c11, c10⟩ := Matrices.ComplexMatrix2.quaternion_entries_of_mem_specialUnitary hA
  have hM : quatMatrix (⟨(A 0 0).re, (A 0 0).im, (A 0 1).re, (A 0 1).im⟩ : ℍ[ℝ]) = A := by
    ext i j
    fin_cases i <;> fin_cases j
    · apply Complex.ext <;> simp [quatMatrix]
    · apply Complex.ext <;> simp [quatMatrix]
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
      rw [c10]
      apply Complex.ext <;> simp [quatMatrix]
    · simp only [Fin.mk_one, Fin.isValue]
      rw [c11]
      apply Complex.ext <;> simp [quatMatrix]
  have hn : Quaternion.normSq (⟨(A 0 0).re, (A 0 0).im, (A 0 1).re, (A 0 1).im⟩ : ℍ[ℝ]) = 1 := by
    have := det_quatMatrix (⟨(A 0 0).re, (A 0 0).im, (A 0 1).re, (A 0 1).im⟩ : ℍ[ℝ])
    rw [hM, hD] at this
    exact_mod_cast this.symm
  exact ⟨⟨_, mem_unitary_of_normSq_eq_one _ hn⟩, Subtype.ext hM⟩
end UnitQuaternions
end YangMills.Construction
end
