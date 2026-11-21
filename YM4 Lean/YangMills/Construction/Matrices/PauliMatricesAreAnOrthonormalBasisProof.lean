import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open PeriodicLattice Matrices.ComplexMatrix2
namespace Matrices.PauliBasis
theorem pauli_mem_hermitianTraceless (a : Fin 3) : pauli a ∈ hermitianTraceless := by apply _root_.YangMills.Construction.LieInnerProductProof.pauli_mem_hermitianTraceless <;> assumption
theorem halfTracePairing_pauli (a b : Fin 3) :
    halfTracePairing (pauli a) (pauli b) = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [halfTracePairing, halfTrace, fullTrace, Matrix.trace_fin_two, pauli, pauliOne, pauliTwo,
      pauliThree] <;>
    norm_num
end Matrices.PauliBasis
end YangMills.Construction
