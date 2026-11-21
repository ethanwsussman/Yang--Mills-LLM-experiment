import YangMills.Construction.Lattice.CellGridProperties
import YangMills.Construction.Lattice.GridCellsAndFaceReflections
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.CellGrid
variable {L : ℕ} {κ : ℤ}
structure GridSymmetry (d : CellGrid L κ) where
  toFun : d.Space → d.Space
  isDistPreserving : BoxTorus.IsDistPreserving toFun
  image_grid : toFun '' (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) =
    (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space)
namespace GridSymmetry
variable {d : CellGrid L κ} (g : d.GridSymmetry)
def pointImage (x : d.GridPoint) : d.GridPoint :=
  ⟨g.toFun x, by
    have hx : g.toFun x ∈ g.toFun '' (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) :=
      ⟨x, x.2, rfl⟩
    rw [g.image_grid] at hx
    exact hx⟩
def edgeImage (e : d.DirectedEdge) : d.DirectedEdge :=
  open Classical in
  if he : ∃ (μ : Fin 4) (s : ℝ), BoxTorus.IsNeighbourStep (g.pointImage e.source) (g.pointImage e.target) μ s
  then ⟨g.pointImage e.source, g.pointImage e.target, he⟩ else e
theorem edgeImage_flip (e : d.DirectedEdge) : g.edgeImage e.flip = (g.edgeImage e).flip := by
  by_cases he : ∃ (μ : Fin 4) (s : ℝ),
      BoxTorus.IsNeighbourStep (g.pointImage e.source) (g.pointImage e.target) μ s
  · have he' : ∃ (μ : Fin 4) (s : ℝ),
        BoxTorus.IsNeighbourStep (g.pointImage e.target) (g.pointImage e.source) μ s := by
      obtain ⟨μ, s, st⟩ := he
      exact ⟨μ, -s, st.symm⟩
    have q : g.edgeImage e = ⟨g.pointImage e.source, g.pointImage e.target, he⟩ := dif_pos he
    have q' : g.edgeImage e.flip = ⟨g.pointImage e.target, g.pointImage e.source, he'⟩ := dif_pos he'
    rw [q, q']
    rfl
  · have he' : ¬ ∃ (μ : Fin 4) (s : ℝ),
        BoxTorus.IsNeighbourStep (g.pointImage e.target) (g.pointImage e.source) μ s := by
      rintro ⟨μ, s, st⟩
      exact he ⟨μ, -s, st.symm⟩
    have q : g.edgeImage e = e := dif_neg he
    have q' : g.edgeImage e.flip = e.flip := dif_neg he'
    rw [q, q']
theorem edgeImage_endpoints (hd : GridLattice.EdgesByDistance d) (e : d.DirectedEdge) :
    (g.edgeImage e).source = g.pointImage e.source ∧ (g.edgeImage e).target = g.pointImage e.target := by
  obtain ⟨e', h₁, h₂⟩ := hd.2 g.toFun g.isDistPreserving g.image_grid e
  have q₁ : e'.source = g.pointImage e.source := Subtype.ext h₁
  have q₂ : e'.target = g.pointImage e.target := Subtype.ext h₂
  have hs : ∃ (μ : Fin 4) (s : ℝ),
      BoxTorus.IsNeighbourStep (g.pointImage e.source) (g.pointImage e.target) μ s := by
    rw [← q₁, ← q₂]
    exact e'.isNeighbour
  rw [edgeImage, dif_pos hs]
  exact ⟨rfl, rfl⟩
def pullback (U : d.GaugeConfig) : d.GaugeConfig :=
  fun e => BoxTorus.edgeVariable U (g.edgeImage e.1)
theorem edgeVariable_pullback (hd : GridLattice.GaugeConfigsAsEdgeMaps d)
    (U : d.GaugeConfig) (e : d.DirectedEdge) :
    BoxTorus.edgeVariable (g.pullback U) e =
      BoxTorus.edgeVariable U (g.edgeImage e) := by
  by_cases he : e.IsForward
  · rw [BoxTorus.edgeVariable, dif_pos he]
    rfl
  · rw [BoxTorus.edgeVariable, dif_neg he]
    show (BoxTorus.edgeVariable U (g.edgeImage e.flip))⁻¹ = _
    rw [g.edgeImage_flip, hd.1 U, inv_inv]
def actOnObservables {X : Type*} (F : d.GaugeConfig → X) : d.GaugeConfig → X :=
  F ∘ g.pullback
end GridSymmetry
variable (d : CellGrid L κ)
def edgesWithin (O : Set d.Space) : Set d.DirectedEdge :=
  {e | (e.source : d.Space) ∈ O ∧ (e.target : d.Space) ∈ O}
def localAlgebra (O : TopologicalSpace.Opens d.Space) : Set (d.GaugeConfig → ℂ) :=
  {F | BoxTorus.IsBoundedBorelOfEdges (d.edgesWithin O) F}
def cellObservables (c : d.spaceCells) : Set (d.GaugeConfig → ℂ) :=
  d.localAlgebra (TopologicalSpace.Opens.interior c.1)
end YangMills.Construction.CellGrid
end
