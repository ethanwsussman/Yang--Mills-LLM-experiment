import YangMills.Construction.ReflectionPositivity.CoordinatesDoubledSpaceAndFunctionalsOfALinkMirror
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.HalfFaceEnergy
variable {D : MirrorData}
def FaceEnergyLocal (C : LinkLevel D) : Prop :=
  ∀ p ∈ C.halfFaces .pos, ∀ U U' : D.FieldSpace,
    C.halfCoords .pos U = C.halfCoords .pos U' →
      PeriodicLattice.plaquetteCost U.1 p = PeriodicLattice.plaquetteCost U'.1 p
def FaceEnergyEqHalf (C : LinkLevel D) : Prop :=
  ∀ p ∈ C.halfFaces .pos, ∀ U : D.FieldSpace,
    PeriodicLattice.plaquetteCost U.1 p = C.faceEnergyOfHalf p (C.halfCoords .pos U)
def HalfActionEqSum (C : LinkLevel D) : Prop :=
  ∀ U : D.FieldSpace, C.halfAction (C.halfCoords .pos U) =
    ∑ᶠ p ∈ C.halfFaces .pos, PeriodicLattice.plaquetteCost U.1 p
def HalfFaceEnergyFacts : Prop :=
  ∀ (D : MirrorData) (C : LinkLevel D),
    FaceEnergyLocal C ∧ FaceEnergyEqHalf C ∧ HalfActionEqSum C
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.HalfFaceEnergy
end
