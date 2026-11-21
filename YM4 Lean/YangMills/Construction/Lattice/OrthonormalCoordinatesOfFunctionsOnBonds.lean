import YangMills.Construction.OneLoop.PauliMatrixComputations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Matrices
namespace BondFunctions.Coordinates
theorem pauliFamily_mem_hermitianTraceless (c : Fin 3) :
    ComplexMatrix2.pauliFamily c ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
end BondFunctions.Coordinates
end YangMills.Construction
end
