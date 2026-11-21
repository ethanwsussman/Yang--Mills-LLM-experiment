import YangMills.Construction.Continuum.FunctionalsOnSeparatedTuples
import YangMills.Construction.LawByMomentsOfTheFlow.CyclicFormulaOfTheLaw
import YangMills.Construction.Torus.LiftsShapeConditionAndCollinearQuadruples
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
open CyclicFormula QuadrupleClasses
open TestSpaces (SepTupleOfCard)
def CyclicFormulaOnSeparatedTuples : Prop :=
  (∀ (n : ℕ) [NeZero n], 2 ≤ n → Odd n → ∀ X : SepTupleOfCard n,
      cyclicMomentFormula n (fun k x => X.1 k (WithLp.ofLp x)) = 0) ∧
    ∀ ϑ ∈ Ioc (0 : ℝ) 1, ∀ X : SepTupleOfCard 4, X.1 ∈ collinearQuadsR4 1 ϑ →
      0 < cyclicMomentFormula 4 (fun k x => X.1 k (WithLp.ofLp x))
end YangMills.Construction.TotalDensitiesGiveASystem
end
