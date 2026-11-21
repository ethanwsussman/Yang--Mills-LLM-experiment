import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.FieldValues
open YangMills.Construction.PeriodicOperators
variable {L k : ℕ}
def IsShiftedField (m : Fin 4 → ℤ) (ζ ζ' : FullField L k) : Prop :=
  (ζ'.1 : Edge L k 0 → Matrices.ComplexMatrix2) =
      pushField (intShift m) (ζ.1 : Edge L k 0 → Matrices.ComplexMatrix2) ∧
    (ζ'.2.1 : Edge L k 0 → Matrices.ComplexMatrix2) =
      pushField (intShift m) (ζ.2.1 : Edge L k 0 → Matrices.ComplexMatrix2) ∧
    (ζ'.2.2 : Edge L k k → Matrices.ComplexMatrix2) =
      pushField (intShift m) (ζ.2.2 : Edge L k k → Matrices.ComplexMatrix2)
def FieldsAndValuesClaim : Prop :=
  ∀ (L : ℕ) (hL : 0 < L) (k : ℕ),
    (∀ ζ : FullField L k,
      backgroundOfCoeffs hL (ζ.pauliCoeffs hL) = (ζ.1 : Edge L k 0 → Matrices.ComplexMatrix2) ∧
      sourceOfCoeffs hL (ζ.pauliCoeffs hL) = (ζ.2.1 : Edge L k 0 → Matrices.ComplexMatrix2) ∧
      coarseOfCoeffs hL (ζ.pauliCoeffs hL) = (ζ.2.2 : Edge L k k → Matrices.ComplexMatrix2) ∧
      vectorOpFn L k hL (ζ.pauliCoeffs hL) = vectorOp ζ ∧
      ghostOpFn L k hL (ζ.pauliCoeffs hL) = ghostOp ζ ∧
      FieldValueFunctions.gaugeFieldOfCoeffs hL (ζ.pauliCoeffs hL) = ζ.gaugeField) ∧
    (∀ f : (fieldPeriodicData L k hL).Carrier → ℂ, ∃ ζ : FullField L k, ζ.pauliCoeffs hL = f) ∧
    (∀ (m : Fin 4 → ℤ) (ζ : FullField L k), ∃ ζ' : FullField L k, IsShiftedField m ζ ζ' ∧
      ζ'.pauliCoeffs hL = shiftField (fieldPeriodicData L k hL) m (ζ.pauliCoeffs hL)) ∧
    ∀ (ζ : FullField L k) (r : ℝ), (∀ κ, ‖ζ.pauliCoeffs hL κ‖ ≤ r) →
      ∀ b : Edge L k 0,
        Matrices.ComplexMatrix2.operatorNorm ((ζ.1 : Edge L k 0 → Matrices.ComplexMatrix2) b) ≤
          Real.sqrt 6 * r
end YangMills.Construction.Tower.FullSpace.FieldValues
end
