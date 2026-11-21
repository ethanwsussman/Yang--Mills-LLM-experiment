import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.MidpointInsertion
def MidpointHasInsertionIntegral : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ)
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma))
    (p C : ℝ), InsertedFieldForm.Hypotheses sigma E p C →
    ∀ G : ℝ → (Fin 4 → ℝ) → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma),
      InsertedFieldForm.IsFieldDensity sigma E G →
      InsertedFieldForm.HasInsertionIntegral sigma E (InsertedFieldForm.midpointField sigma G)
end YangMills.Construction.MidpointInsertion
end
