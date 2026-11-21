import YangMills.Construction.Lattice.ActionOfIsometriesAndAlgebrasOfAGridDatum
import YangMills.Construction.Lattice.MapsInducedOnTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GridMirror
open BoxTorus
variable {L : ℕ} {κ : ℤ}
def IsMirrorReflection {d : CellGrid L κ} (g : d.GridSymmetry) (μ : Fin 4) (c : ℝ) : Prop :=
  (∃ z : ℤ, c = PeriodicLattice.meshSize L κ * ((z : ℝ) + 1 / 2)) ∧
    d.IsInducedMap g.toFun (TorusDescent.coordReflection μ c)
abbrev HalfEdge (d : CellGrid L κ) (H : Set d.Space) : Type :=
  {b : d.ForwardEdge // b.1.LiesIn H}
def mirrorPairedPoints {d : CellGrid L κ} (g : d.GridSymmetry) (H : Set d.Space) :
    Set d.GridPoint :=
  {y | (y : d.Space) ∈ H ∧ ∃ b : d.DirectedEdge, b.source = g.pointImage y ∧ b.target = y}
abbrev MirrorPairedPoint {d : CellGrid L κ} (g : d.GridSymmetry) (H : Set d.Space) : Type :=
  ↥(mirrorPairedPoints g H)
def mirrorEdge {d : CellGrid L κ} {g : d.GridSymmetry} {H : Set d.Space}
    (y : MirrorPairedPoint g H) : d.DirectedEdge where
  source := g.pointImage y.1
  target := y.1
  isNeighbour := by
    obtain ⟨-, e, he₁, he₂⟩ := y.2
    rw [← he₁, ← he₂]
    exact e.isNeighbour
def transverseEdges {d : CellGrid L κ} (g : d.GridSymmetry) (H : Set d.Space) (μ : Fin 4) :
    Set (HalfEdge d H) :=
  {b | b.1.1.source ∈ mirrorPairedPoints g H ∧ b.1.1.target ∈ mirrorPairedPoints g H ∧
    ¬ b.1.1.HasAxis μ}
abbrev TransverseEdge {d : CellGrid L κ} (g : d.GridSymmetry) (H : Set d.Space) (μ : Fin 4) :
    Type :=
  ↥(transverseEdges g H μ)
variable {d : CellGrid L κ} {g : d.GridSymmetry} {H : Set d.Space} {μ : Fin 4}
def TransverseEdge.start (b : TransverseEdge g H μ) : MirrorPairedPoint g H :=
  ⟨b.1.1.1.source, b.2.1⟩
def TransverseEdge.finish (b : TransverseEdge g H μ) : MirrorPairedPoint g H :=
  ⟨b.1.1.1.target, b.2.2.1⟩
def mirrorHolonomy (U : d.GaugeConfig) (b : TransverseEdge g H μ) :
    Conventions.StandingParameters.gaugeGroup :=
  edgeVariable U b.1.1.1 * (edgeVariable U (mirrorEdge b.finish))⁻¹ *
    (edgeVariable U (g.edgeImage b.1.1.1))⁻¹ * edgeVariable U (mirrorEdge b.start)
def mirrorFaceEnergy (U : d.GaugeConfig) (b : TransverseEdge g H μ) : ℝ :=
  1 - (1 / 2) * (Matrices.ComplexMatrix2.fullTrace
    (mirrorHolonomy U b : Matrices.ComplexMatrix2)).re
def halfFaces (d : CellGrid L κ) (H : Set d.Space) : Set d.Face :=
  {p | ∀ x ∈ p.vertexSet, (x : d.Space) ∈ H}
def halfAction (d : CellGrid L κ) (H : Set d.Space) (U : d.GaugeConfig) : ℝ :=
  ∑ᶠ p : halfFaces d H, faceEnergy U p.1
end YangMills.Construction.GridMirror
end
