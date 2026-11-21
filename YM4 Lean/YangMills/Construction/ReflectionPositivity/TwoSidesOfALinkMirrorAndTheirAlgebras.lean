import YangMills.Construction.Lattice.ImagesOfBondsAndPlaquettesUnderLatticeIsometries
import YangMills.Construction.ReflectionPositivity.ReflectionsMirrorsAndSlabsAtOneCutoff
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.CutoffMirrors
namespace MirrorData
variable (D : MirrorData)
abbrev Vertex : Type := PeriodicLattice.Site D.L D.m (D.K : ℕ)
abbrev Edge : Type := PeriodicLattice.Bond D.L D.m (D.K : ℕ)
abbrev Face : Type := PeriodicLattice.Plaquette D.L D.m (D.K : ℕ)
abbrev FieldSpace : Type := PeriodicLattice.compactGaugeFields D.L D.m (D.K : ℕ)
def linkValues (S : Set D.Edge) (U : D.FieldSpace) : S → Matrices.ComplexMatrix2.specialUnitary :=
  fun e => ⟨U.1 e.1, U.2.1 e.1 (mem_univ _)⟩
def IsBoundedMeasurableInLinks (S : Set D.Edge) (F : D.FieldSpace → ℂ) : Prop :=
  ∃ Φ : (S → Matrices.ComplexMatrix2.specialUnitary) → ℂ,
    Measurable[borel (S → Matrices.ComplexMatrix2.specialUnitary)] Φ ∧ (∃ M : ℝ, ∀ v, ‖Φ v‖ ≤ M) ∧
    F = fun U => Φ (D.linkValues S U)
end MirrorData
namespace LinkLevel
variable {D : MirrorData} (C : LinkLevel D)
def halfVertices (σ : SlabSide) : Set D.Torus := (D.latticeSubgroup : Set D.Torus) ∩ C.openSlab σ
def halfEdges (σ : SlabSide) : Set D.Edge :=
  {e | e.IsPositivelyOriented ∧ (e.source : D.Torus) ∈ C.halfVertices σ ∧
    (e.target : D.Torus) ∈ C.halfVertices σ}
def transversalEdges : Set D.Edge :=
  {e | e.IsPositivelyOriented ∧ e ∉ C.halfEdges .pos ∧ e ∉ C.halfEdges .neg}
def halfFaces (σ : SlabSide) : Set D.Face :=
  {p | ∀ x ∈ p.vertices, (x : D.Torus) ∈ C.halfVertices σ}
def transversalFaces : Set D.Face :=
  {p | p ∉ C.halfFaces .pos ∧ p ∉ C.halfFaces .neg}
def Straddles (e : D.Edge) : Prop :=
  ((e.source : D.Torus) ∈ C.halfVertices .neg ∧ (e.target : D.Torus) ∈ C.halfVertices .pos) ∨
    ((e.source : D.Torus) ∈ C.halfVertices .pos ∧ (e.target : D.Torus) ∈ C.halfVertices .neg)
def IsStraddlingTransversal (e : D.Edge) : Prop :=
  e ∈ C.transversalEdges ∧ C.Straddles e
open Classical in
def orientedAcross (e : D.Edge) : D.Edge :=
  if (e.source : D.Torus) ∈ C.halfVertices .neg ∧ (e.target : D.Torus) ∈ C.halfVertices .pos then e
  else e.opposite
def endOn (σ : SlabSide) (e : D.Edge) : D.Vertex :=
  match σ with
  | .neg => (C.orientedAcross e).source
  | .pos => (C.orientedAcross e).target
theorem orientedAcross_eq_or (e : D.Edge) :
    C.orientedAcross e = e ∨ C.orientedAcross e = e.opposite := by
  unfold orientedAcross
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl
theorem endOn_mem {e : D.Edge} (h : C.Straddles e) (σ : SlabSide) :
    (C.endOn σ e : D.Torus) ∈ C.halfVertices σ := by
  by_cases h' : (e.source : D.Torus) ∈ C.halfVertices .neg ∧
      (e.target : D.Torus) ∈ C.halfVertices .pos
  · have hx : C.orientedAcross e = e := if_pos h'
    cases σ
    · simpa [endOn, hx] using h'.2
    · simpa [endOn, hx] using h'.1
  · have hx : C.orientedAcross e = e.opposite := if_neg h'
    have h'' := h.resolve_left h'
    cases σ
    · simpa [endOn, hx, PeriodicLattice.Bond.opposite] using h''.1
    · simpa [endOn, hx, PeriodicLattice.Bond.opposite] using h''.2
def transversalVariable (e : D.Edge) (U : D.FieldSpace) : Matrices.ComplexMatrix2 :=
  U.1 (C.orientedAcross e)
def IsReflectedEdge (e e' : D.Edge) : Prop :=
  (e'.source : D.Torus) = C.refl e.source ∧ (e'.target : D.Torus) = C.refl e.target
open Classical in
def reflectedEdge (e : D.Edge) : D.Edge :=
  if h : ∃ e', C.IsReflectedEdge e e' then h.choose else e
theorem bondMap_eq_reflectedEdge (s : PeriodicLattice.TorusLatticeSymmetry D.L D.m D.K)
    (hs : s.toFun = C.refl) (e : D.Edge) : s.bondMap e = C.reflectedEdge e := by
  have key : ∀ e', s.IsBondImage e e' ↔ C.IsReflectedEdge e e' := by
    intro e'
    constructor
    · intro h
      have h₁ : e'.source = s.pointMap e.source := congrArg Prod.fst h
      have h₂ : e'.target = s.pointMap e.target := congrArg Prod.snd h
      exact ⟨by rw [h₁, ← hs]; rfl, by rw [h₂, ← hs]; rfl⟩
    · rintro ⟨h₁, h₂⟩
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change (e'.source : D.Torus) = s.toFun e.source
        rw [h₁, hs]
      · change (e'.target : D.Torus) = s.toFun e.target
        rw [h₂, hs]
  by_cases h : ∃ e', C.IsReflectedEdge e e'
  · have h' : ∃ e', s.IsBondImage e e' := h.imp fun e' => (key e').2
    have q₁ : s.bondMap e = h'.choose := dif_pos h'
    have q₂ : C.reflectedEdge e = h.choose := dif_pos h
    rw [q₁, q₂]
    exact s.isBondImage_unique h'.choose_spec ((key _).2 h.choose_spec)
  · have h' : ¬∃ e', s.IsBondImage e e' := fun ⟨e', he⟩ => h ⟨e', (key e').1 he⟩
    have q₁ : s.bondMap e = e := dif_neg h'
    have q₂ : C.reflectedEdge e = e := dif_neg h
    rw [q₁, q₂]
open Classical in
def positiveReflectedEdge (e : D.Edge) : D.Edge :=
  if (C.reflectedEdge e).IsPositivelyOriented then C.reflectedEdge e else (C.reflectedEdge e).opposite
def ContainsMirrorAxis (_C : LinkLevel D) (p : D.Face) : Prop :=
  D.dir = p.firstAxis ∨ D.dir = p.secondAxis
def complementaryAxis (_C : LinkLevel D) (p : D.Face) : Fin 4 :=
  if p.firstAxis = D.dir then p.secondAxis else p.firstAxis
def lowerEdge (_C : LinkLevel D) (p : D.Face) : D.Edge :=
  PeriodicLattice.Bond.forwardFrom p.origin D.dir
def upperEdge (p : D.Face) : D.Edge :=
  PeriodicLattice.Bond.forwardFrom
    (p.origin + PeriodicLattice.unitStep D.L D.m (D.K : ℕ) (C.complementaryAxis p)) D.dir
def HasStraddlingEdges (p : D.Face) : Prop :=
  C.IsStraddlingTransversal (C.lowerEdge p) ∧ C.IsStraddlingTransversal (C.upperEdge p)
def lowerCorner (σ : SlabSide) (p : D.Face) : D.Vertex :=
  C.endOn σ (C.lowerEdge p)
def upperCorner (σ : SlabSide) (p : D.Face) : D.Vertex :=
  C.endOn σ (C.upperEdge p)
def halfAlgebra (σ : SlabSide) : Set (D.FieldSpace → ℂ) :=
  {F | D.IsBoundedMeasurableInLinks (C.halfEdges σ) F}
end LinkLevel
end YangMills.Construction.ReflectionPositivity.CutoffMirrors
end
