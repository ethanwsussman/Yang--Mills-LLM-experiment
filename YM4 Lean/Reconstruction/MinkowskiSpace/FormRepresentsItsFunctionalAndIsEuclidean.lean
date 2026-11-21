import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.InsertedFieldForm
def RepresentsOfTimeOrdered : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ)
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma))
    (p C : ℝ), Hypotheses sigma E p C →
    ∀ (A : ℝ → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma)) (q K : ℝ),
      FieldForms.IsBoundedFieldForm E (FieldFormConditions.vacuumState sigma) A q K →
      HasTimeOrderedIntegral sigma E A →
        RepresentsEuclideanSchwinger sigma E A
end YangMills.Construction.InsertedFieldForm
end
