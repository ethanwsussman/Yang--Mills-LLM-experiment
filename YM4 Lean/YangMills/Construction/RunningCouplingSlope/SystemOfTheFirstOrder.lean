import YangMills.Construction.RunningCouplingSlope.TriplesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
variable {L n k : ℕ}
def linearTransport (ξ : LevelForms L n k) : (m : ℕ) → Edge L n k m → Matrices.ComplexMatrix2
  | 0 => ξ.1
  | m + 1 =>
    if h : m < k then
      linearSmoothing L n k m (linearTransport ξ m) + (ξ.2 ⟨m, h⟩ : Edge L n k (m + 1) → Matrices.ComplexMatrix2)
    else 0
def hessianAtIdentity (a : ℝ) (ξ ξ' : LevelForms L n k) : ℝ :=
  (traceFinsumPairing (edgeCoboundary (ξ.1 : Edge L n k 0 → Matrices.ComplexMatrix2))
    (edgeCoboundary (ξ'.1 : Edge L n k 0 → Matrices.ComplexMatrix2))).re +
    a * ∑ i : Fin k, (edgeFormPairing (ξ.2 i : Edge L n k (i + 1) → Matrices.ComplexMatrix2)
      (ξ'.2 i : Edge L n k (i + 1) → Matrices.ComplexMatrix2)).re
structure SolvesFirstOrderSystem (a : ℝ) (B : edgeFormSpace L n k k) (t : LevelTriple L n k) : Prop where
  top_eq : linearTransport t.1 k = B
  pairing_eq_hessian : ∀ η : LevelForms L n k,
    levelPairing (formValues t.2.1) (formValues η) = hessianAtIdentity a t.1 η
  pairing_eq_adjoint : ∀ η : LevelForms L n k, levelPairing (formValues t.2.1) (formValues η) =
    (edgeFormPairing (t.2.2 : Edge L n k k → Matrices.ComplexMatrix2) (linearTransport η k)).re
end YangMills.Construction.RunningCouplingSlope
end
