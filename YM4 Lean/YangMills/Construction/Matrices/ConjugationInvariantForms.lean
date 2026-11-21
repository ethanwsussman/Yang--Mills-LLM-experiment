import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.ConjugationInvariants
open YangMills.Construction.OneLoop
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
end YangMills.Construction.Matrices.ConjugationInvariants
end
