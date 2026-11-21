import YangMills.Construction.ReflectionPositivity.CoordinatesDoubledSpaceAndFunctionalsOfALinkMirror
import YangMills.Construction.ReflectionPositivity.HeightOverALinkPosition
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors
def LinkLevel.transversalHolonomy {D : MirrorData} (C : LinkLevel D) (p : D.Face)
    (U : D.FieldSpace) : YangMills.Construction.Matrices.ComplexMatrix2 :=
  C.transversalVariable (C.lowerEdge p) U * U.1 (C.cornerEdge .pos p) *
    (C.transversalVariable (C.upperEdge p) U)⁻¹ * (U.1 (C.cornerEdge .neg p))⁻¹
namespace HalfSpaces
variable {D : MirrorData}
abbrev shiftBy (x : D.Vertex) (ν : Fin 4) : D.Vertex :=
  x + YangMills.Construction.PeriodicLattice.unitStep D.L D.m (D.K : ℕ) ν
def levelAt (C : LinkLevel D) (j : ℤ) : ℝ := C.pos + ((j : ℝ) + 1 / 2) * D.spacing
def VertexSplitting (C : LinkLevel D) : Prop :=
  {r | ∃ x : D.Vertex, C.centeredRep (x : D.Torus) = r} =
      {r | ∃ j : ℤ, -(D.sitesPerSide : ℤ) ≤ j ∧ j ≤ (D.sitesPerSide : ℤ) - 1 ∧ r = levelAt C j} ∧
    (∀ (x : D.Vertex) (j : ℤ), -(D.sitesPerSide : ℤ) ≤ j → j ≤ -1 →
      C.centeredRep (x : D.Torus) = levelAt C j → (x : D.Torus) ∈ C.halfVertices .neg) ∧
    (∀ (x : D.Vertex) (j : ℤ), 0 ≤ j → j ≤ (D.sitesPerSide : ℤ) - 1 →
      C.centeredRep (x : D.Torus) = levelAt C j → (x : D.Torus) ∈ C.halfVertices .pos) ∧
    (∀ x : D.Vertex, (x : D.Torus) ∉ C.mirrorSet) ∧
    (D.latticeSubgroup : Set D.Torus) = C.halfVertices .pos ∪ C.halfVertices .neg ∧
    Disjoint (C.halfVertices .pos) (C.halfVertices .neg) ∧
    C.refl '' C.halfVertices .pos = C.halfVertices .neg ∧
    C.refl '' C.halfVertices .neg = C.halfVertices .pos
def HeightStep (C : LinkLevel D) : Prop :=
  (∀ (x : D.Vertex) (ν : Fin 4), ν ≠ D.dir →
    C.centeredRep (shiftBy x ν : D.Torus) = C.centeredRep (x : D.Torus)) ∧
  (∀ x : D.Vertex, C.centeredRep (x : D.Torus) ≠ C.pos + D.side / 2 - D.spacing / 2 →
    C.centeredRep (shiftBy x D.dir : D.Torus) = C.centeredRep (x : D.Torus) + D.spacing) ∧
  ∀ x : D.Vertex, C.centeredRep (x : D.Torus) = C.pos + D.side / 2 - D.spacing / 2 →
    C.centeredRep (shiftBy x D.dir : D.Torus) = C.pos - D.side / 2 + D.spacing / 2
def TransversalEdgeProperties (C : LinkLevel D) : Prop :=
  ∀ b ∈ C.transversalEdges, b.IsParallelToAxis D.dir ∧ C.IsStraddlingTransversal b ∧
    (C.endOn .pos b : D.Torus) = C.refl (C.endOn .neg b) ∧
    ∀ U : D.FieldSpace,
      C.transversalVariable b U = U.1 b ∨ C.transversalVariable b U = (U.1 b)⁻¹
def PullbackOnPositiveEdges (C : LinkLevel D) (s : D.Symmetry) : Prop :=
  ∀ (U : D.FieldSpace), ∀ b ∈ C.halfEdges .pos,
    (¬b.IsParallelToAxis D.dir →
      MirrorData.Symmetry.pullback s U.1 b = U.1 (C.positiveReflectedEdge b)) ∧
    (b.IsParallelToAxis D.dir →
      MirrorData.Symmetry.pullback s U.1 b = (U.1 (C.positiveReflectedEdge b))⁻¹)
def TransversalFaceProperties (C : LinkLevel D) : Prop :=
  ∀ p ∈ C.transversalFaces, C.ContainsMirrorAxis p ∧
    C.lowerEdge p ∈ C.transversalEdges ∧ C.upperEdge p ∈ C.transversalEdges ∧
    C.HasStraddlingEdges p ∧
    p.vertices = {C.lowerCorner .pos p, C.lowerCorner .neg p,
      C.upperCorner .pos p, C.upperCorner .neg p} ∧
    (∀ σ : SlabSide, C.upperCorner σ p = shiftBy (C.lowerCorner σ p) (C.complementaryAxis p)) ∧
    (∀ σ : SlabSide, (C.cornerEdge σ p).source = C.lowerCorner σ p ∧
      (C.cornerEdge σ p).target = C.upperCorner σ p) ∧
    C.cornerEdge .pos p ∈ C.halfEdges .pos ∧
    C.cornerEdge .neg p ∈ C.halfEdges .neg ∧
    C.positiveReflectedEdge (C.cornerEdge .pos p) = C.cornerEdge .neg p ∧
    ∀ U : D.FieldSpace,
      (1 / 2 : ℝ) * (YangMills.Construction.Matrices.ComplexMatrix2.fullTrace
          (YangMills.Construction.PeriodicLattice.plaquetteHolonomy U.1 p)).re =
        (1 / 2 : ℝ) * (YangMills.Construction.Matrices.ComplexMatrix2.fullTrace
          (C.transversalHolonomy p U)).re
def HalfSpaceStructure : Prop :=
  ∀ (D : MirrorData) (C : LinkLevel D),
    VertexSplitting C ∧ HeightStep C ∧ TransversalEdgeProperties C ∧
    BijOn C.positiveReflectedEdge (C.halfEdges .pos) (C.halfEdges .neg) ∧
    (∀ (σ : SlabSide), ∀ p ∈ C.halfFaces σ, p.edges ⊆ C.halfEdges σ) ∧
    TransversalFaceProperties C ∧
    (∀ p : D.Face, p.barycenter ∈ C.openSlab .pos → p ∈ C.halfFaces .pos) ∧
    ∃ s : D.Symmetry, s.toFun = C.refl ∧ PullbackOnPositiveEdges C s ∧
      MirrorData.Symmetry.faceImage s '' C.halfFaces .pos = C.halfFaces .neg
end HalfSpaces
end YangMills.Construction.ReflectionPositivity.CutoffMirrors
end
