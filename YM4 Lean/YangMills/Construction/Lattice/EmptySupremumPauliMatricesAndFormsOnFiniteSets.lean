import YangMills.Construction.Lattice.LieValuedBondFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Matrices PeriodicLattice
namespace Matrices.ComplexMatrix2
def pauliOne : ComplexMatrix2 := !![0, 1; 1, 0]
def pauliTwo : ComplexMatrix2 := !![0, -Complex.I; Complex.I, 0]
def pauliThree : ComplexMatrix2 := !![1, 0; 0, -1]
def pauli : Fin 3 → ComplexMatrix2 := ![pauliOne, pauliTwo, pauliThree]
end Matrices.ComplexMatrix2
namespace PeriodicLattice
def scaledPairingSum {S : Type*} [Finite S] (t : ℝ) (f g : S → ↥ComplexMatrix2.traceless) : ℂ :=
  (t : ℂ) * ∑ᶠ s : S, halfTracePairing (f s : ComplexMatrix2) (g s : ComplexMatrix2)
end PeriodicLattice
end YangMills.Construction
