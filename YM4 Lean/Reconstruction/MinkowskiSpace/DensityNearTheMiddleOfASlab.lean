import Reconstruction.MinkowskiSpace.FieldFormOfAFunctionalDefs
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
noncomputable section
namespace YangMills.Construction.InsertedFieldForm
def CentralDensityFormula : Prop :=
  ∀ (sigma : TestSpaces.SepTuple → ℝ)
    (E : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp (FieldFormConditions.StateSpace sigma))
    (p C : ℝ), Hypotheses sigma E p C →
    ∀ (η : ℝ) (h : (Fin 4 → ℝ) → ℂ) (F : ReflectionPositivity.TupleForm.PositiveSpan)
      (χ : FieldFormConditions.StateSpace sigma), 0 < η → η ≤ 1 →
      h ∈ TestSpaces.c1CompactSupp (Set.univ : Set (Fin 4 → ℝ)) →
      (∀ y ∈ tsupport h, y - (3 * η) • FieldFormConditions.timeUnitVec ∈ centralBox η) →
        ⟪χ, insertedState sigma h ((6 * η) • FieldFormConditions.timeUnitVec) F⟫_ℂ =
          ∫ a, h ((3 * η) • FieldFormConditions.timeUnitVec + a) *
            ⟪χ, smoothedFieldOp sigma E η a (FieldFormConditions.stateOf sigma F)⟫_ℂ
end YangMills.Construction.InsertedFieldForm
end
