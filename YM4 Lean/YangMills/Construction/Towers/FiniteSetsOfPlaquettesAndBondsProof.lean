import YangMills.Construction.Lattice.QuotientLatticesAndNeighbours
import YangMills.Construction.Towers.FiniteSetsOfPlaquettesAndBonds
import YangMills.Construction.Towers.PlaquettesOfABond
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FaceEdgeFinsets
section Abstract
variable {B P : Type} (edges : P → List B) (good : B → Prop) (p₀ : P)
theorem finite_faces_and_edges_of_locallyFinite (hgood : ∀ p, ∀ b ∈ edges p, good b)
    (hfin : ∀ F : Set {b // good b}, F.Finite →
      {p : P | ∃ b ∈ F, (b : B) ∈ edges p}.Finite)
    (e₀ : B) (he₀ : e₀ ∈ edges p₀) :
    (∀ F : Set B, F.Finite → (∀ b ∈ F, good b) →
      {p : P | ∃ b ∈ F, b ∈ edges p}.Finite ∧
      (F = ∅ → {p : P | ∃ b ∈ F, b ∈ edges p} = ∅) ∧
      ({p : P | ∃ b ∈ F, b ∈ edges p} ∪ {p₀}).Finite ∧
      ({p : P | ∃ b ∈ F, b ∈ edges p} ∪ {p₀}).Nonempty) ∧
    (∀ F : Set B, F.Finite → (∀ b ∈ F, good b) →
      {b | b ∈ edges p₀ ∨ ∃ p ∈ {p : P | ∃ b ∈ F, b ∈ edges p}, b ∈ edges p}.Finite ∧
      {b | b ∈ edges p₀ ∨ ∃ p ∈ {p : P | ∃ b ∈ F, b ∈ edges p}, b ∈ edges p}.Nonempty ∧
      ∀ b ∈ {b | b ∈ edges p₀ ∨ ∃ p ∈ {p : P | ∃ b ∈ F, b ∈ edges p}, b ∈ edges p}, good b) := by
  have hS : ∀ F : Set B, F.Finite → (∀ b ∈ F, good b) →
      {p : P | ∃ b ∈ F, b ∈ edges p}.Finite := by
    intro F hF hg
    refine (hfin (Subtype.val ⁻¹' F) (hF.preimage Subtype.val_injective.injOn)).subset ?_
    rintro p ⟨b, hb, hbp⟩
    exact ⟨⟨b, hg b hb⟩, hb, hbp⟩
  refine ⟨fun F hF hg => ⟨hS F hF hg, ?_, (hS F hF hg).union (finite_singleton _),
    ⟨p₀, Or.inr rfl⟩⟩, fun F hF hg => ⟨?_, ⟨e₀, Or.inl he₀⟩, ?_⟩⟩
  · rintro rfl
    ext p
    simp
  · have hEq : {b | b ∈ edges p₀ ∨ ∃ p ∈ {p : P | ∃ b ∈ F, b ∈ edges p}, b ∈ edges p} =
        {b | b ∈ edges p₀} ∪
          ⋃ p ∈ {p : P | ∃ b ∈ F, b ∈ edges p}, {b | b ∈ edges p} := by
      ext b
      simp only [mem_ofPred_eq, mem_union, mem_iUnion, exists_prop]
    rw [hEq]
    exact (List.finite_toSet _).union ((hS F hF hg).biUnion fun p _ => List.finite_toSet _)
  · rintro b (hb | ⟨p, -, hb⟩)
    · exact hgood _ _ hb
    · exact hgood _ _ hb
end Abstract
theorem faceEdges_positive {L n k j : ℕ} (f : Face L n k j) :
    ∀ b ∈ faceEdges f, b.IsPositivelyOriented := by
  have hFwd : ∀ (x : Vertex L n k j) (μ : Fin 4),
      (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented :=
    fun x μ => ⟨μ, add_sub_cancel_left x _⟩
  intro b hb
  simp only [faceEdges, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> exact hFwd _ _
theorem fullSpace_faceEdges_positive {L k j : ℕ} (f : FullSpace.Face L k j) :
    ∀ b ∈ FullSpace.faceEdges f, b.IsPositivelyOriented := by
  have hFwd : ∀ (x : FullSpace.Vertex L k j) (μ : Fin 4),
      (InfiniteLattice.Link.forwardFrom x μ).IsPositivelyOriented :=
    fun x μ => ⟨μ, add_sub_cancel_left x _⟩
  intro b hb
  simp only [FullSpace.faceEdges, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> exact hFwd _ _
theorem holdsOnTorus_of {L n k j : ℕ} (hFaces : FacesContainingEdge.Periodic L n k j)
    (hQuot : QuotientLattices.IsQuotientLattice L n k j) : HoldsOnTorus L n k j := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hP⟩ := hQuot
  have : Finite (Face L n k j) := hP
  have H := finite_faces_and_edges_of_locallyFinite faceEdges
    PeriodicLattice.Bond.IsPositivelyOriented
    (baseFace L n k j) faceEdges_positive hFaces.2.2
    (PeriodicLattice.Bond.forwardFrom (baseFace L n k j).origin (baseFace L n k j).firstAxis)
    (by simp [faceEdges])
  exact ⟨⟨(PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j)).zero_mem,
    faceEdges_positive⟩, H.1, H.2, toFinite _, mem_univ _⟩
theorem holdsOnFullSpace_of {L k j : ℕ} (hFaces : FacesContainingEdge.OnFullSpace L k j) :
    Unbounded.HoldsOnFullSpace L k j := by
  have H := finite_faces_and_edges_of_locallyFinite FullSpace.faceEdges
    InfiniteLattice.Link.IsPositivelyOriented
    (Unbounded.baseFace L k j) fullSpace_faceEdges_positive hFaces.2.2
    (InfiniteLattice.Link.forwardFrom (Unbounded.baseFace L k j).corner
      (Unbounded.baseFace L k j).lowAxis)
    (by simp [FullSpace.faceEdges])
  exact ⟨⟨(InfiniteLattice.latticeSubgroup (meshAt L k j)).zero_mem,
    fullSpace_faceEdges_positive⟩, H.1, H.2⟩
theorem facesAndEdgesFinite_of (h₁ : FacesContainingEdge.Holds)
    (h₂ : QuotientLattices.TorusAndSpaceLatticeProperties) : FacesAndEdgesFinite := by
  intro L hL k j hjk
  exact ⟨fun n hn => holdsOnTorus_of ((h₁ L hL k j hjk).1 n hn) (h₂ L hL n j k hn hjk).2.1,
    holdsOnFullSpace_of (h₁ L hL k j hjk).2⟩
end YangMills.Construction.Tower.FaceEdgeFinsets
end
