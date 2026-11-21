import YangMills.Construction.LawByMomentsOfTheFlow.CyclicFormulaOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace CyclicFormula
open TestFunctions
def ExteriorSquareTraceOfOddInversionProduct : Prop :=
  (∀ A : Matrix (Fin 4) (Fin 4) ℝ, A * A.transpose = 1 → A.det = -1 → exteriorSquareTrace A = 0) ∧
  ∀ l : List EuclideanFourSpace, Odd l.length → (∀ x ∈ l, x ≠ 0) →
    exteriorSquareTrace (l.map inversionMatrix).prod = 0
end CyclicFormula
end YangMills.Construction
end
