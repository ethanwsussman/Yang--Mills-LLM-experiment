import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposes
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def pauliCoords (Z : ↥traceless) (a : Fin 3) : ℂ := halfTracePairing (pauli a) (Z : ComplexMatrix2)
theorem pauliCombination_pauliCoords (Z : ↥traceless) :
    pauliCombination (pauliCoords Z) = (Z : ComplexMatrix2) := by
  have hZ : (Z : ComplexMatrix2) 1 1 = -(Z : ComplexMatrix2) 0 0 := by
    have h : Matrix.trace (Z : ComplexMatrix2) = 0 := Z.2
    rw [Matrix.trace_fin_two] at h
    linear_combination h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliCombination, pauliCoords, halfTracePairing, halfTrace, fullTrace, Fin.sum_univ_three,
      pauli, pauliOne, pauliTwo, pauliThree, Matrix.trace_fin_two, Matrix.mul_apply, hZ] <;>
    ring_nf <;> simp <;> ring
def hermitianNormFin3 (z : Fin 3 → ℂ) : ℝ := Real.sqrt (∑ a, ‖z a‖ ^ 2)
def pauliCoordNorm (Z : ↥traceless) : ℝ := hermitianNormFin3 (pauliCoords Z)
end YangMills.Construction.Matrices.ComplexMatrix2
