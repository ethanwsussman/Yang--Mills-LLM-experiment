import YangMills.Construction.ClusterExpansionOfAStep.FlowOfTheExpansion
import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.SummableBoundsOfTheFlow.FlowOfTheNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FloorBounds
open RenormalizationStepParameters TorusLumps CouplingFlow
structure FlowAboveFloor (T : ParameterAssignment) (y c X : ℝ) : Prop where
  admissible : (T.stepParameters y).Admissible
  slopeConst_gt : 10 < slopeConst T.side
  c_nonneg : 0 ≤ c
  le_floor : y ≤ X
  drop_two_sided : ∀ (β : ℝ) (i j : ℕ), i ≤ j → (∀ l < j, X ≤ (couplingFlow (T.stepParameters y) β l).1) →
    3 / 4 * slopeConst T.side * ((j : ℝ) - i) - 2 * c ≤
        (couplingFlow (T.stepParameters y) β i).1 - (couplingFlow (T.stepParameters y) β j).1 ∧
      (couplingFlow (T.stepParameters y) β i).1 - (couplingFlow (T.stepParameters y) β j).1 ≤
        5 / 4 * slopeConst T.side * ((j : ℝ) - i) + 2 * c
  hasExpansion : ∀ (β : ℝ) (t : ℕ), X ≤ β → (∀ l < t, X ≤ (couplingFlow (T.stepParameters y) β l).1) →
    HasExpansion (T.stepParameters y) t (couplingFlow (T.stepParameters y) β t).1
      (couplingFlow (T.stepParameters y) β t).2
end YangMills.Construction.FloorBounds
end
