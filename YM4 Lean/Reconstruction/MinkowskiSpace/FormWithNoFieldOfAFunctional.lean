import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.InsertedFieldForm
def ZeroFieldForm : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ)
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma))
    (p C : ℝ), Hypotheses sigma E p C →
    FieldForms.IsBoundedFieldForm E (FieldFormConditions.vacuumState sigma) (fun _ => 0) 0 1
end YangMills.Construction.InsertedFieldForm
end
