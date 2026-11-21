import YangMills.Construction.Matrices.NormExpLogConjugationLemmas
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2
namespace ConjugationLemmas
private theorem inv_mem_unitary {V : ComplexMatrix2} (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    V⁻¹ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.NormExpLogConj.unitary_inv_mem <;> assumption
private theorem isUnit_of_unitary {V : ComplexMatrix2}
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) : IsUnit V :=
  IsUnit.of_mul_eq_one _ (Matrix.mem_unitaryGroup_iff.mp hV)
private theorem operatorNorm_unitary_mul_mul (X u v : ComplexMatrix2)
    (hu : u ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hv : v ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    operatorNorm (u * X * v) = operatorNorm X := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.NormExpLogConj.operatorNorm_unitary_mul_mul <;> assumption
private theorem mul_inv_of_isUnit {T : ComplexMatrix2} (hT : IsUnit T) : T * T⁻¹ = 1 :=
  Matrix.mul_nonsing_inv T ((Matrix.isUnit_iff_isUnit_det T).mp hT)
private theorem inv_mul_of_isUnit {T : ComplexMatrix2} (hT : IsUnit T) : T⁻¹ * T = 1 :=
  Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp hT)
private theorem logSeries_conj {T X : ComplexMatrix2} (hT : IsUnit T)
    (hX : operatorNorm (X - 1) < 1) :
    logSeries (T * X * T⁻¹) = T * logSeries X * T⁻¹ := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.NormExpLogConj.logSeries_conj <;> assumption
private theorem matExp_conj {T : ComplexMatrix2} (hT : IsUnit T) (Z : ComplexMatrix2) :
    T * matExp Z * T⁻¹ = matExp (T * Z * T⁻¹) := by
  let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
  obtain ⟨t, rfl⟩ := hT
  have hinv : ((t : ComplexMatrix2))⁻¹ = ((t⁻¹ : ComplexMatrix2ˣ) : ComplexMatrix2) := Matrix.inv_eq_right_inv t.mul_inv
  simp only [matExp]
  rw [hinv]
  exact (NormedSpace.exp_units_conj t Z).symm
end ConjugationLemmas
open ConjugationLemmas in
theorem operatorNormUnderConjugation : OperatorNormUnderConjugation := by
  refine ⟨operatorNorm_unitary_mul_mul, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X V hV
    exact operatorNorm_unitary_mul_mul X V V⁻¹ hV (inv_mem_unitary hV)
  · intro V hV
    have h : V⁻¹ - 1 = V⁻¹ * (1 - V) * 1 := by
      rw [mul_one, mul_sub, mul_one, inv_mul_of_isUnit (isUnit_of_unitary hV)]
    rw [h, operatorNorm_unitary_mul_mul _ _ _ (inv_mem_unitary hV) (one_mem _)]
    simp only [operatorNorm]
    exact norm_sub_rev _ _
  · intro V V' hV hV'
    have h : V * V'⁻¹ - 1 = 1 * (V - V') * V'⁻¹ := by
      rw [one_mul, sub_mul, mul_inv_of_isUnit (isUnit_of_unitary hV')]
    rw [h, operatorNorm_unitary_mul_mul _ _ _ (one_mem _) (inv_mem_unitary hV')]
  · intro T Z hT
    exact matExp_conj hT Z
  · intro T X hT hX _
    exact logSeries_conj hT hX
  · intro T X hT hX
    have h : T * X * T⁻¹ - 1 = T * (X - 1) * T⁻¹ := by
      rw [mul_sub, sub_mul, mul_one, mul_inv_of_isUnit (isUnit_of_unitary hT)]
    rw [h, operatorNorm_unitary_mul_mul _ _ _ hT (inv_mem_unitary hT)]
    exact hX
end YangMills.Construction.Matrices.ComplexMatrix2
