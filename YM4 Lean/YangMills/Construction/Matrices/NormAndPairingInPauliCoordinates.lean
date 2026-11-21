import YangMills.Construction.Matrices.PauliCoordinatesAndHermitianNorm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.PauliNormPairing
open YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.PeriodicLattice
def opNormWrt (ν : ↥traceless → ℝ) (T : ↥traceless →ₗ[ℂ] ↥traceless) : ℝ :=
  sSup ((fun Z => ν (T Z)) '' {Z | ν Z ≤ 1})
def linOpNorm (T : ↥traceless →ₗ[ℂ] ↥traceless) : ℝ :=
  opNormWrt (fun Z => operatorNorm (Z : ComplexMatrix2)) T
def linOpPauliNorm (T : ↥traceless →ₗ[ℂ] ↥traceless) : ℝ := opNormWrt pauliCoordNorm T
def PairingNormCoords : Prop :=
  ∀ z w : Fin 3 → ℂ,
    halfTracePairing (pauliCombination z) (pauliCombination w) = ∑ i, z i * w i ∧
    hermitianNormFin3 z ≤ operatorNorm (pauliCombination z) ∧
    operatorNorm (pauliCombination z) ≤ Real.sqrt 2 * hermitianNormFin3 z
def PairingBounds : Prop :=
  (∀ z w : Fin 3 → ℂ,
    ‖halfTracePairing (pauliCombination z) (pauliCombination w)‖ ≤
        hermitianNormFin3 z * hermitianNormFin3 w ∧
    hermitianNormFin3 z * hermitianNormFin3 w ≤
        operatorNorm (pauliCombination z) * operatorNorm (pauliCombination w)) ∧
  ∀ z : Fin 3 → ℂ, operatorNorm (pauliCombination z) ≤
    2 * sSup ((fun E : ↥traceless => ‖halfTracePairing (E : ComplexMatrix2) (pauliCombination z)‖) ''
      {E | operatorNorm (E : ComplexMatrix2) ≤ 1})
def OpNormsComparable : Prop :=
  ∀ T : ↥traceless →ₗ[ℂ] ↥traceless,
    linOpPauliNorm T ≤ Real.sqrt 2 * linOpNorm T ∧ linOpNorm T ≤ Real.sqrt 2 * linOpPauliNorm T
def Statement : Prop :=
  PairingNormCoords ∧ PairingBounds ∧ OpNormsComparable
end YangMills.Construction.Matrices.PauliNormPairing
