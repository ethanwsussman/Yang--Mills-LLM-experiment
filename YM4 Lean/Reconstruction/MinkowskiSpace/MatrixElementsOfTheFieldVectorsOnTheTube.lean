import Reconstruction.MinkowskiSpace.BoundaryValuesOnTheTube
import Reconstruction.MinkowskiSpace.VectorsAtRealPointsDefs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology
noncomputable section
namespace YangMills.Construction.TubeMatrixElements
def Statement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (Ω : H)
    (T : ℝ → OneLoopNotation.BddOp H) (p C : ℝ),
    FieldForms.IsBoundedFieldForm P Ω T p C →
    ∀ (m : ℕ) (x : H),
      WightmanTheory.IsHolomorphicOnTube (RealPointVectors.tubeMatrixElement P Ω T x (m := m)) ∧
      (∀ z ∈ WightmanTheory.tubeTuples (m + 1), ‖RealPointVectors.tubeMatrixElement P Ω T x z‖ ≤
        ‖x‖ * ((2 : ℝ) ^ p * C) ^ (m + 1) *
          ∏ k, (min 1 (MinkowskiSpace.tubeGap (z k)))⁻¹ ^ (FieldForms.ceilExponent p (m + 1)).toNat) ∧
      (∀ w : Fin (m + 1) → MinkowskiSpace.ComplexVec4,
        ⟪x, FieldForms.stateVector P Ω T (m + 1) w⟫_ℂ =
          RealPointVectors.tubeMatrixElement P Ω T x (MinkowskiSpace.diffCoords w)) ∧
      ∀ Y ∈ RealPointVectors.futureConeTuples (m + 1), ∀ f : TestSpaces.PointTuple (m + 1) → ℂ,
        f ∈ TestSpaces.schwartzSet (m + 1) →
        ProjectionMeasures.HasWeakIntegrandData Set.univ
            (RealPointVectors.shiftedStateVector P Ω T Y) f ∧
        ⟪x, RealPointVectors.smearedState P Ω T Y f⟫_ℂ =
          TubeBoundary.pairing (RealPointVectors.tubeMatrixElement P Ω T x) Y
            (RealPointVectors.diffCoords f)
end YangMills.Construction.TubeMatrixElements
end
