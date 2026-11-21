import YangMills.Construction.LawByMomentsOfTheFlow.CyclicFormulaOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace CyclicFormula
open TestFunctions
def InversionMatrixProperties : Prop :=
  (∀ x : EuclideanFourSpace, (inversionMatrix x).transpose = inversionMatrix x) ∧
  (∀ x : EuclideanFourSpace, inversionMatrix x * inversionMatrix x = 1) ∧
  (∀ x : EuclideanFourSpace, x ≠ 0 → (inversionMatrix x).det = -1) ∧
  (∀ (c : ℝ) (x : EuclideanFourSpace), c ≠ 0 → inversionMatrix (c • x) = inversionMatrix x) ∧
  inversionMatrix 0 = 1 ∧
  (∀ A : Matrix (Fin 4) (Fin 4) ℝ,
    exteriorSquareTrace A = ((Matrix.trace A) ^ 2 - Matrix.trace (A * A)) / 2) ∧
  exteriorSquareTrace 1 = 6
end CyclicFormula
end YangMills.Construction
end
