import Reconstruction.MinkowskiSpace.BoundaryValuesOnTheTube
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.SmearedBoundaryVectors
section Vectors
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (Ω : H)
  (T : ℝ → OneLoopNotation.BddOp H)
structure Properties (p C : ℝ) : Prop where
  isBoundaryLimit_testState : ∀ (m : ℕ) (f : TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ TestSpaces.schwartzSet (m + 1) →
    RealPointVectors.IsBoundaryLimit P Ω T f (RealPointVectors.testState P Ω T (m + 1) f)
  eq_testState_of_isBoundaryLimit : ∀ (m : ℕ) (f : TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ TestSpaces.schwartzSet (m + 1) →
    ∀ v : H, RealPointVectors.IsBoundaryLimit P Ω T f v →
      v = RealPointVectors.testState P Ω T (m + 1) f
  testState_linearCombination : ∀ (m : ℕ) (f g : TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ TestSpaces.schwartzSet (m + 1) → g ∈ TestSpaces.schwartzSet (m + 1) → ∀ a b : ℂ,
      RealPointVectors.testState P Ω T (m + 1) (a • f + b • g) =
        a • RealPointVectors.testState P Ω T (m + 1) f +
          b • RealPointVectors.testState P Ω T (m + 1) g
  norm_testState_le : ∀ (m : ℕ) (f : TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ TestSpaces.schwartzSet (m + 1) →
    ‖RealPointVectors.testState P Ω T (m + 1) f‖ ≤
      4 * ((2 : ℝ) ^ p * C) ^ (m + 1) * RealPointVectors.fieldFormNorm p f
  inner_testState_eq_boundaryValue : ∀ (m : ℕ) (f : TestSpaces.PointTuple (m + 1) → ℂ),
    f ∈ TestSpaces.schwartzSet (m + 1) →
    ∀ x : H, ⟪x, RealPointVectors.testState P Ω T (m + 1) f⟫_ℂ =
      TubeBoundary.boundaryValue (RealPointVectors.tubeMatrixElement P Ω T x) 0
        (RealPointVectors.diffCoords f)
end Vectors
def Statement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (Ω : H)
    (T : ℝ → OneLoopNotation.BddOp H) (p C : ℝ),
    FieldForms.IsBoundedFieldForm P Ω T p C →
    Properties P Ω T p C
end YangMills.Construction.SmearedBoundaryVectors
end
