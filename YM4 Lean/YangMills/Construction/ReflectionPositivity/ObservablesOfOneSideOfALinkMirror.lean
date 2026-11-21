import YangMills.Construction.ReflectionPositivity.CoordinatesDoubledSpaceAndFunctionalsOfALinkMirror
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors.OneSideObservables
variable {D : MirrorData} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
def FacesInHalf (C : LinkLevel D) (f : D.Torus → E) : Prop :=
  ∀ p : D.Face, f p.barycenter ≠ 0 →
    p ∈ C.halfFaces .pos ∧
      ∀ b ∈ p.edges, b ∈ C.halfEdges .pos ∧
        (b.source : D.Torus) ∈ C.openSlab .pos ∧ (b.target : D.Torus) ∈ C.openSlab .pos
def ObservableEqHalfSum (C : LinkLevel D) (f : D.Torus → E) : Prop :=
  ∀ U : D.FieldSpace, PeriodicLattice.smearedObservable f U.1 =
    ∑ᶠ p ∈ C.halfFaces .pos, PeriodicLattice.plaquetteCost U.1 p • f p.barycenter
def ObservablesMemHalfAlgebra (ι : E → ℂ) (C : LinkLevel D) (f : D.Torus → E) : Prop :=
  (fun U : D.FieldSpace => ι (PeriodicLattice.smearedObservable f U.1)) ∈ C.halfAlgebra .pos ∧
    (fun U : D.FieldSpace => ι (D.centredObservable f U.1)) ∈ C.halfAlgebra .pos
def ReflectImage (C : LinkLevel D) (f : D.Torus → E) : Prop :=
  (∀ U : D.FieldSpace, PeriodicLattice.smearedObservable f (C.reflectField U).1 =
    PeriodicLattice.smearedObservable (C.reflectFn f) U.1) ∧
  D.supp (C.reflectFn f) ⊆ C.openSlab .neg ∧
  PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling
      (PeriodicLattice.smearedObservable (C.reflectFn f)) =
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.coupling (PeriodicLattice.smearedObservable f) ∧
  ∀ U : D.FieldSpace, D.centredObservable f (C.reflectField U).1 =
    D.centredObservable (C.reflectFn f) U.1
def BoundedFunClaims (ι : E → ℂ) (C : LinkLevel D) (f : D.Torus → E) : Prop :=
  TestFunctions.IsBoundedFun f → D.supp f ⊆ C.openSlab .pos →
    FacesInHalf C f ∧ ObservableEqHalfSum C f ∧
      ObservablesMemHalfAlgebra ι C f ∧ ReflectImage C f
def HalfSpaceObservables : Prop :=
  ∀ (D : MirrorData) (C : LinkLevel D),
    (∀ f : D.Torus → ℝ, BoundedFunClaims Complex.ofReal C f) ∧
      ∀ f : D.Torus → ℂ, BoundedFunClaims id C f
end YangMills.Construction.ReflectionPositivity.CutoffMirrors.OneSideObservables
end
