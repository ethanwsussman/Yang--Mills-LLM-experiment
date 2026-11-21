import YangMills.Construction.Towers.SymmetriesOfTheAbelianOperatorsProof
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate Matrix.Norms.L2Operator
open YangMills.Construction.Tower.AbelianFieldFacts YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.AbelianFieldDensity YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.Tower.Charges
theorem raisingPauli_eq_single : raisingPauli = !![0, 1; 0, 0] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.raisingPauli_eq_matrix <;> assumption
theorem loweringPauli_eq_single : loweringPauli = !![0, 0; 1, 0] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.loweringPauli_eq_matrix <;> assumption
theorem cartanPhase_eq_diag (θ : ℝ) :
    cartanPhase θ = !![Complex.exp (Complex.I * θ), 0; 0, Complex.exp (-(Complex.I * θ))] := by apply _root_.YangMills.Construction.Tower.AbelianActionGradient.cartanPhase_eq_diagonal <;> assumption
theorem cartanPhase_inv_eq (θ : ℝ) :
    (cartanPhase θ)⁻¹ = !![Complex.exp (-(Complex.I * θ)), 0; 0, Complex.exp (Complex.I * θ)] := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.cartanPhase_inv_eq_diag <;> assumption
theorem chargeAlgebra_holds : ChargeAlgebra := by
  have hz := ComplexMatrix2.pauliFamily_apply.2.2
  refine ⟨fun θ => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : Complex.exp (2 * Complex.I * θ) =
        Complex.exp (Complex.I * θ) * Complex.exp (Complex.I * θ) := by
      rw [← Complex.exp_add]; ring_nf
    rw [ComplexMatrix2.conjugateBy, cartanPhase_inv_eq, cartanPhase_eq_diag, raisingPauli_eq_single, e]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have e : Complex.exp (-(2 * Complex.I * θ)) =
        Complex.exp (-(Complex.I * θ)) * Complex.exp (-(Complex.I * θ)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [ComplexMatrix2.conjugateBy, cartanPhase_inv_eq, cartanPhase_eq_diag, loweringPauli_eq_single, e]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [raisingPauli_eq_single, loweringPauli_eq_single, hz, Ring.lie_def]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [raisingPauli_eq_single, loweringPauli_eq_single]
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]
  · rw [raisingPauli_eq_single]
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]
  · rw [loweringPauli_eq_single]
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]
  · rw [raisingPauli_eq_single, hz]
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]
  · rw [loweringPauli_eq_single, hz]
    simp [ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]
theorem exists_entries_of_mem_hermitianTraceless {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ∃ (p : ℝ) (q : ℂ), X = !![(p : ℂ), q; conj q, -(p : ℂ)] := by
  obtain ⟨hh, ht⟩ := hX
  have h00 : conj (X 0 0) = X 0 0 := by
    have := congrFun (congrFun hh 0) 0
    simpa [Matrix.conjTranspose_apply] using this.symm
  have h10 : X 1 0 = conj (X 0 1) := by
    have := congrFun (congrFun hh 1) 0
    simpa [Matrix.conjTranspose_apply] using this
  have h11 : X 1 1 = -X 0 0 := by
    have h : Matrix.trace X = 0 := ht
    rw [Matrix.trace_fin_two] at h
    linear_combination h
  obtain ⟨p, hp⟩ := Complex.conj_eq_iff_real.mp h00
  refine ⟨p, X 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hp, h10, h11]
theorem operatorNorm_sq_of_entries (p : ℝ) (q : ℂ) :
    ComplexMatrix2.operatorNorm !![(p : ℂ), q; conj q, -(p : ℂ)] ^ 2 = p ^ 2 + ‖q‖ ^ 2 := by
  set X : ComplexMatrix2 := !![(p : ℂ), q; conj q, -(p : ℂ)] with hXdef
  have hstar : star X = X := by
    rw [Matrix.star_eq_conjTranspose, hXdef]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hq : q * conj q = ((‖q‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsq : X * X = ((p ^ 2 + ‖q‖ ^ 2 : ℝ) : ℂ) • (1 : ComplexMatrix2) := by
    rw [hXdef]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hq, sq, mul_comm q] <;> ring_nf <;>
      simp [hq, mul_comm] <;> ring
  have hn : ‖X‖ * ‖X‖ = p ^ 2 + ‖q‖ ^ 2 := by
    have h := CStarRing.norm_star_mul_self (x := X)
    rw [hstar, hsq, norm_smul, CStarRing.norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at h
    exact h.symm
  rw [ComplexMatrix2.operatorNorm, sq]
  exact hn
theorem formsChargeDecomposition_holds (s : ℝ) : FormsChargeDecomposition s := by
  intro B hB e
  obtain ⟨p, q, h⟩ := exists_entries_of_mem_hermitianTraceless (hB.1 e.1 e.2)
  have hz := ComplexMatrix2.pauliFamily_apply.2.2
  have hd : FullSpace.diagonalComponent B e = p := by
    simp [FullSpace.diagonalComponent, h, hz, ComplexMatrix2.halfTrace, ComplexMatrix2.fullTrace,
      Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have ho : FullSpace.offDiagonalComponent B e = q := by
    simp [FullSpace.offDiagonalComponent, h, loweringPauli_eq_single, ComplexMatrix2.halfTrace,
      ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hd, ho, h]
  refine ⟨?_, operatorNorm_sq_of_entries p q⟩
  rw [hz, raisingPauli_eq_single, loweringPauli_eq_single]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
theorem chargeAlgebraAndForms_holds : ChargeAlgebraAndForms :=
  ⟨chargeAlgebra_holds, fun _ _ => formsChargeDecomposition_holds _⟩
end YangMills.Construction.Tower.Charges
end
