import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.TimeOrderedVectors
open ProjectionMeasures OneLoopNotation FieldFormConditions FieldForms InsertedFieldForm
def Represents : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ) (E : FourBorelSet → BddOp (StateSpace sigma)) (p C : ℝ),
    Hypotheses sigma E p C →
    ∀ G : ℝ → (Fin 4 → ℝ) → BddOp (StateSpace sigma), IsFieldDensity sigma E G →
      ∀ ℘ D : ℝ, IsBoundedFieldForm E (vacuumState sigma) (midpointField sigma G) ℘ D →
        HasTimeOrderedIntegral sigma E (midpointField sigma G)
end YangMills.Construction.TimeOrderedVectors
end
