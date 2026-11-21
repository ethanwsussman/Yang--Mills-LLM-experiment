import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.FieldOperatorUniqueness
open ProjectionMeasures OneLoopNotation FieldFormConditions InsertedFieldForm
def Unique : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ) (E : FourBorelSet → BddOp (StateSpace sigma)) (p C : ℝ),
    Hypotheses sigma E p C →
    ∀ A B : ℝ → BddOp (StateSpace sigma),
      HasInsertionIntegral sigma E A → HasInsertionIntegral sigma E B →
        ∀ s : ℝ, 0 < s → B s = A s
end YangMills.Construction.FieldOperatorUniqueness
end
