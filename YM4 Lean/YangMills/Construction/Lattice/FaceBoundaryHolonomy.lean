import YangMills.Construction.Lattice.RectangularGrids
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BoxTorus.FaceBoundary
open YangMills.Construction.BoxTorus
variable {L : ℕ} {κ : ℤ} {ℓ : Fin 4 → ℝ}
def cornerCycle (p : Face L κ ℓ) : Fin 4 → GridPoint L κ ℓ :=
  ![p.corner, p.corner + gridStep L κ ℓ p.dir₁,
    p.corner + gridStep L κ ℓ p.dir₁ + gridStep L κ ℓ p.dir₂,
    p.corner + gridStep L κ ℓ p.dir₂]
def EdgesJoinCycle (z : Fin 4 → GridPoint L κ ℓ) (b : Fin 4 → DirectedEdge L κ ℓ) : Prop :=
  ∀ i, (b i).source = z i ∧ (b i).target = z (i + 1)
def cycleProduct (U : GaugeConfig L κ ℓ) (b : Fin 4 → DirectedEdge L κ ℓ) :
    Conventions.StandingParameters.gaugeGroup :=
  edgeVariable U (b 0) * edgeVariable U (b 1) * edgeVariable U (b 2) * edgeVariable U (b 3)
def boundaryEdges (p : Face L κ ℓ) : Set (DirectedEdge L κ ℓ) :=
  {b | ∃ i, b.source = cornerCycle p i ∧ b.target = cornerCycle p (i + 1)}
def EdgesAroundFace {L : ℕ} {κ : ℤ} (d : CellGrid L κ) (p : d.Face) : Prop :=
  (∀ i, ∃ b : d.DirectedEdge, b.source = cornerCycle p i ∧ b.target = cornerCycle p (i + 1)) ∧
  (∀ i, ¬ ∃ b : d.DirectedEdge, b.ends = {cornerCycle p i, cornerCycle p (i + 2)}) ∧
  ∀ b : Fin 4 → d.DirectedEdge, EdgesJoinCycle (cornerCycle p) b →
    ∀ U : d.GaugeConfig, faceHolonomy U p = cycleProduct U b
def EnergyAnyCycleOrder {L : ℕ} {κ : ℤ} (d : CellGrid L κ) (p : d.Face) : Prop :=
  ∀ (z : Fin 4 → d.GridPoint) (b : Fin 4 → d.DirectedEdge),
    Function.Injective z → Set.range z = p.vertexSet → EdgesJoinCycle z b →
    ∀ U : d.GaugeConfig,
      faceEnergy U p = 1 - (1 / 2) *
        (Matrices.ComplexMatrix2.fullTrace (cycleProduct U b : Matrices.ComplexMatrix2)).re
def FaceEnergyRegularity {L : ℕ} {κ : ℤ} (d : CellGrid L κ) (p : d.Face) : Prop :=
  Continuous (fun U : d.GaugeConfig => faceEnergy U p) ∧
  (∀ U : d.GaugeConfig, faceEnergy U p ∈ Set.Icc (0 : ℝ) 2) ∧
  IsBoundedBorelOfEdges (boundaryEdges p)
    (fun U : d.GaugeConfig => ((faceEnergy U p : ℝ) : ℂ))
def FaceBoundaryProperty : Prop :=
  ∀ (L : ℕ) (κ : ℤ) (d : CellGrid L κ) (p : d.Face),
    EdgesAroundFace d p ∧ EnergyAnyCycleOrder d p ∧ FaceEnergyRegularity d p
end YangMills.Construction.BoxTorus.FaceBoundary
end
