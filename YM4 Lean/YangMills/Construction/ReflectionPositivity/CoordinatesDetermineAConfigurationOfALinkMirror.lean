import YangMills.Construction.ReflectionPositivity.CoordinatesDoubledSpaceAndFunctionalsOfALinkMirror
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkCoordinates
def CoordinatesDetermineField : Prop :=
  ∀ (D : MirrorData) (C : LinkLevel D),
    (∀ (uPos : C.halfEdges .pos → Matrices.ComplexMatrix2.specialUnitary)
        (uNeg : C.halfEdges .neg → Matrices.ComplexMatrix2.specialUnitary)
        (v : C.transversalEdges → Matrices.ComplexMatrix2.specialUnitary),
      (∃! U : D.FieldSpace, C.HasCoords U uPos uNeg v) ∧
        C.HasCoords (C.fieldOfCoords uPos uNeg v) uPos uNeg v) ∧
    ∀ (σ : SlabSide) (u : C.halfEdges σ → Matrices.ComplexMatrix2.specialUnitary),
      ∃ U : D.FieldSpace, C.halfCoords σ U = u
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.LinkCoordinates
end
