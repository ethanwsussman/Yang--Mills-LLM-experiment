import YangMills.Construction.ReflectionPositivity.PlaquetteActionReadsOneSideOfALinkMirror
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Matrices
namespace ReflectionPositivity.CutoffMirrors.HalfFaceEnergy
variable {D : MirrorData}
theorem forwardFrom_mem_halfEdges (C : LinkLevel D) {x : D.Vertex} {μ : Fin 4}
    (hx : (x : D.Torus) ∈ C.halfVertices .pos)
    (hy : ((x + PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) μ : D.Vertex) : D.Torus) ∈
      C.halfVertices .pos) :
    PeriodicLattice.Bond.forwardFrom x μ ∈ C.halfEdges .pos := by
  refine ⟨⟨μ, ?_⟩, hx, hy⟩
  show x + PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) μ - x =
    PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) μ
  exact add_sub_cancel_left x _
theorem boundary_mem_halfEdges (C : LinkLevel D) {f : D.Face}
    (hf : f ∈ C.halfFaces .pos) :
    PeriodicLattice.Bond.forwardFrom f.origin f.firstAxis ∈ C.halfEdges .pos ∧
      PeriodicLattice.Bond.forwardFrom
        (f.origin + PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) f.firstAxis) f.secondAxis ∈
          C.halfEdges .pos ∧
      PeriodicLattice.Bond.forwardFrom
        (f.origin + PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) f.secondAxis) f.firstAxis ∈
          C.halfEdges .pos ∧
      PeriodicLattice.Bond.forwardFrom f.origin f.secondAxis ∈ C.halfEdges .pos := by
  set a : D.Vertex := PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) f.firstAxis
  set b : D.Vertex := PeriodicLattice.unitStep D.L D.m ((D.K : ℕ) : ℤ) f.secondAxis
  have hv : ∀ x : D.Vertex, x ∈ ({f.origin, f.origin + a, f.origin + a + b, f.origin + b} :
      Set D.Vertex) → (x : D.Torus) ∈ C.halfVertices .pos := hf
  have v₁ : (f.origin : D.Torus) ∈ C.halfVertices .pos :=
    hv f.origin (Set.mem_insert _ _)
  have v₂ : ((f.origin + a : D.Vertex) : D.Torus) ∈ C.halfVertices .pos :=
    hv (f.origin + a) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have v₃ : ((f.origin + a + b : D.Vertex) : D.Torus) ∈ C.halfVertices .pos :=
    hv (f.origin + a + b) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have v₄ : ((f.origin + b : D.Vertex) : D.Torus) ∈ C.halfVertices .pos :=
    hv (f.origin + b)
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_singleton _))))
  have v₅ : ((f.origin + b + a : D.Vertex) : D.Torus) ∈ C.halfVertices .pos := by
    have e : f.origin + b + a = f.origin + a + b := add_right_comm _ _ _
    rw [e]
    exact v₃
  exact ⟨forwardFrom_mem_halfEdges C v₁ v₂, forwardFrom_mem_halfEdges C v₂ v₃,
    forwardFrom_mem_halfEdges C v₄ v₅, forwardFrom_mem_halfEdges C v₁ v₄⟩
theorem field_eq_of_halfCoords_eq (C : LinkLevel D) {U V : D.FieldSpace}
    (h : C.halfCoords .pos U = C.halfCoords .pos V) {e : D.Edge}
    (he : e ∈ C.halfEdges .pos) : U.1 e = V.1 e :=
  congrArg (fun g : ComplexMatrix2.specialUnitary => (g : ComplexMatrix2)) (congrFun h ⟨e, he⟩)
theorem faceEnergyLocal_holds (C : LinkLevel D) : FaceEnergyLocal C := by
  intro f hf U V h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := boundary_mem_halfEdges C hf
  have hopp : ∀ (W : D.FieldSpace) (e : D.Edge), W.1 e.opposite = (W.1 e)⁻¹ :=
    fun W e => W.2.2 e (Set.mem_univ _)
  have hol : PeriodicLattice.plaquetteHolonomy U.1 f = PeriodicLattice.plaquetteHolonomy V.1 f := by
    unfold PeriodicLattice.plaquetteHolonomy PeriodicLattice.pathHolonomy
      PeriodicLattice.Plaquette.boundaryBonds
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
      List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
      hopp U, hopp U, hopp V, hopp V, field_eq_of_halfCoords_eq C h h₁,
      field_eq_of_halfCoords_eq C h h₂, field_eq_of_halfCoords_eq C h h₃,
      field_eq_of_halfCoords_eq C h h₄]
  unfold PeriodicLattice.plaquetteCost
  rw [hol]
theorem faceEnergyEqHalf_holds (C : LinkLevel D) : FaceEnergyEqHalf C := by
  intro f hf U
  have hex : ∃ r : ℝ, ∀ V : D.FieldSpace,
      C.halfCoords .pos V = C.halfCoords .pos U →
        PeriodicLattice.plaquetteCost V.1 f = r :=
    ⟨PeriodicLattice.plaquetteCost U.1 f, fun V h => faceEnergyLocal_holds C f hf V U h⟩
  exact Classical.epsilon_spec hex U rfl
theorem halfActionEqSum_holds (C : LinkLevel D) : HalfActionEqSum C := by
  intro U
  unfold LinkLevel.halfAction
  exact finsum_mem_congr rfl fun f hf => (faceEnergyEqHalf_holds C f hf U).symm
theorem halfFaceEnergyFacts_holds : HalfFaceEnergyFacts := fun _ C =>
  ⟨faceEnergyLocal_holds C, faceEnergyEqHalf_holds C, halfActionEqSum_holds C⟩
end ReflectionPositivity.CutoffMirrors.HalfFaceEnergy
end YangMills.Construction
end
