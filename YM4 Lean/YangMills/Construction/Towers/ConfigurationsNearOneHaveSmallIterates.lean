import YangMills.Construction.Towers.TheTwoOperatorFunctionsAsFunctionsOfValues
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.SmallIterates
open YangMills.Construction.PeriodicOperators
def SmallIteratesNearOne : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    (∃ υ : ℕ → ℝ, (∀ j < k, 0 < υ j) ∧ (∀ j, j + 1 < k → υ j ≤ υ (j + 1)) ∧
      υ (k - 1) = polydiscRadius L ∧
      ∀ W ∈ fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
        (∀ b, Matrices.ComplexMatrix2.operatorNorm (W b - 1) < υ 0) →
        W ∈ smallIterateFields L k ∧
          ∀ j < k, ∀ b, Matrices.ComplexMatrix2.operatorNorm (complexIter L k j W b - 1) < υ j) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ f, IsSupBelow (fieldPeriodicData L k hL) f ρ →
      FieldValueFunctions.gaugeFieldOfCoeffs hL f ∈ smallIterateFields L k
end YangMills.Construction.Tower.FullSpace.SmallIterates
end
