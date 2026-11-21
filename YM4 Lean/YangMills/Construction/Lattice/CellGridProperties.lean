import YangMills.Construction.Lattice.RectangularGrids
import Mathlib
set_option autoImplicit false
open MeasureTheory
open YangMills.Construction.PeriodicLattice (meshSize)
noncomputable section
namespace YangMills.Construction.GridLattice
variable {L : ℕ} {κ : ℤ}
def meshMultiplesMod (d : CellGrid L κ) (μ : Fin 4) : Set (AddCircle (d.sideLengths μ)) :=
  {t | ∃ n : ℤ, t = (((n : ℝ) * meshSize L κ : ℝ) : AddCircle (d.sideLengths μ))}
def PointCountsAndLifts (d : CellGrid L κ) : Prop :=
  (∀ μ, d.sideLengths μ / meshSize L κ = d.counts μ * (d.cellLength / meshSize L κ) ∧
    ∃ N : ℕ, (N : ℝ) = d.sideLengths μ / meshSize L κ ∧ (meshMultiplesMod d μ).ncard = N ∧
      Even N ∧ 4 ≤ N) ∧
  (∀ w w' : Fin 4 → ℝ, BoxTorus.projection d.sideLengths w = BoxTorus.projection d.sideLengths w' →
    (∀ μ, |w μ - w' μ| ≤ 3 * meshSize L κ) → w = w') ∧
  ∀ (x : d.GridPoint) (w : Fin 4 → ℝ), BoxTorus.IsLiftOf w (x : d.Space) →
    ∃ n : Fin 4 → ℤ, ∀ μ, w μ = (n μ : ℝ) * meshSize L κ
def EdgesAndFaces (d : CellGrid L κ) : Prop :=
  (∀ (ν ν' : Fin 4) (σ σ' : ℝ), (σ = 1 ∨ σ = -1) → (σ' = 1 ∨ σ' = -1) →
    BoxTorus.projection d.sideLengths ((σ * meshSize L κ) • BoxTorus.basisVector ν) =
      BoxTorus.projection d.sideLengths ((σ' * meshSize L κ) • BoxTorus.basisVector ν') →
    ν = ν' ∧ σ = σ') ∧
  (∀ b : d.DirectedEdge,
    (∃! ν, b.HasAxis ν) ∧ (∃! S, b.IsSegmentSet S) ∧
    (∀ ν, b.flip.HasAxis ν ↔ b.HasAxis ν) ∧
    (∀ S, b.flip.IsSegmentSet S ↔ b.IsSegmentSet S) ∧
    Xor b.IsForward b.flip.IsForward) ∧
  (∀ p : d.Face, p.vertexSet.ncard = 4) ∧
  (∀ b b' : d.DirectedEdge, b.IsForward → b'.IsForward → b.ends = b'.ends → b = b') ∧
  ∀ p p' : d.Face, p.vertexSet = p'.vertexSet → p = p'
def GaugeConfigsAsEdgeMaps (d : CellGrid L κ) : Prop :=
  (∀ (U : d.GaugeConfig) (b : d.DirectedEdge),
    BoxTorus.edgeVariable U b.flip = (BoxTorus.edgeVariable U b)⁻¹) ∧
  ∀ u : d.DirectedEdge → Conventions.StandingParameters.gaugeGroup, (∀ b, u b.flip = (u b)⁻¹) →
    ∃! U : d.GaugeConfig, ∀ b, BoxTorus.edgeVariable U b = u b
def EdgesByDistance (d : CellGrid L κ) : Prop :=
  (∀ x y : d.GridPoint, (∃ b : d.DirectedEdge, b.ends = {x, y}) ↔
    BoxTorus.torusDist (x : d.Space) (y : d.Space) = meshSize L κ) ∧
  ∀ g : d.Space → d.Space, BoxTorus.IsDistPreserving g →
    g '' (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) =
      (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) →
    ∀ b : d.DirectedEdge, ∃ b' : d.DirectedEdge,
      (b'.source : d.Space) = g (b.source : d.Space) ∧ (b'.target : d.Space) = g (b.target : d.Space)
def BoltzmannWeightIntegrable (d : CellGrid L κ) : Prop :=
  CompactSpace d.GaugeConfig ∧
  ∀ β : ℝ, 0 < β →
    Continuous (fun U : d.GaugeConfig => Real.exp (-β * d.wilsonAction U)) ∧
    (∀ U : d.GaugeConfig, 0 < Real.exp (-β * d.wilsonAction U)) ∧
    Integrable (fun U : d.GaugeConfig => Real.exp (-β * d.wilsonAction U))
      (BoxTorus.haarConfigMeasure L κ d.sideLengths) ∧
    0 < ∫ U : d.GaugeConfig, Real.exp (-β * d.wilsonAction U)
      ∂(BoxTorus.haarConfigMeasure L κ d.sideLengths)
def Properties : Prop :=
  ∀ (L : ℕ) (κ : ℤ) (d : CellGrid L κ),
    PointCountsAndLifts d ∧ EdgesAndFaces d ∧ GaugeConfigsAsEdgeMaps d ∧ EdgesByDistance d ∧
      BoltzmannWeightIntegrable d
end YangMills.Construction.GridLattice
end
