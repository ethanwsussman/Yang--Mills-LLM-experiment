import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ChessboardSetup
variable (D : ChessboardSetup)
abbrev PeriodicPlaquette : Type := PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ)
def linkFamily (eL : D.cubicPeriod.DirectedEdge ≃ D.PeriodicLink) (U : D.cubicPeriod.GaugeConfig) :
    D.PeriodicLink → Matrices.ComplexMatrix2 :=
  fun b => (BoxTorus.edgeVariable U (eL.symm b) : Matrices.ComplexMatrix2)
def CubicPeriodIsPeriodSubgroup : Prop :=
  (D.cubicPeriod.subgroup : Set AmbientSpace) =
      range (TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m)) ∧
    ∀ μ, (D.cubicPeriod.mult μ : ℝ) = PeriodicLattice.torusSide D.L D.m / D.mesh ∧
      D.cubicPeriod.mult μ = 2 * (D.L : ℤ) ^ ((D.m : ℕ) + (D.K : ℕ))
def TorusEquiv (e : D.cubicPeriod.TorusSpace ≃+ D.Torus) : Prop :=
  IsHomeomorph e ∧
    (∀ y, e (D.cubicPeriod.proj y) = D.proj y) ∧
    e '' (D.cubicPeriod.gridSubgroup : Set D.cubicPeriod.TorusSpace) =
      (PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ) : Set D.Torus) ∧
    ∀ u v, D.cubicPeriod.torusDist u v = TorusMetric.torusEuclidNorm (e u - e v)
def LinkEquiv (e : D.cubicPeriod.TorusSpace ≃+ D.Torus)
    (eL : D.cubicPeriod.DirectedEdge ≃ D.PeriodicLink) : Prop :=
  (∀ b : D.cubicPeriod.DirectedEdge,
    ((eL b).source : D.Torus) = e (b.source : D.cubicPeriod.TorusSpace) ∧
      ((eL b).target : D.Torus) = e (b.target : D.cubicPeriod.TorusSpace)) ∧
    (∀ b : D.cubicPeriod.DirectedEdge, b.IsForward ↔ (eL b).IsPositivelyOriented) ∧
    ∀ b : D.cubicPeriod.DirectedEdge, eL b.flip = (eL b).opposite
def PlaquetteEquiv (e : D.cubicPeriod.TorusSpace ≃+ D.Torus)
    (eP : D.cubicPeriod.Face ≃ D.PeriodicPlaquette) : Prop :=
  ∀ p : D.cubicPeriod.Face,
    ((eP p).origin : D.Torus) = e (p.corner : D.cubicPeriod.TorusSpace) ∧
      (eP p).firstAxis = p.dir₁ ∧ (eP p).secondAxis = p.dir₂ ∧
      (fun x : D.cubicPeriod.GridPoint => e (x : D.cubicPeriod.TorusSpace)) '' p.vertexSet =
        (fun y : PeriodicLattice.Site D.L D.m ((D.K : ℕ) : ℤ) => (y : D.Torus)) '' (eP p).vertices ∧
      e (D.cubicPeriod.faceCenter p) = (eP p).barycenter
def FieldEquiv (eL : D.cubicPeriod.DirectedEdge ≃ D.PeriodicLink) : Prop :=
  BijOn (D.linkFamily eL) univ (PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) ∧
    D.cubicPeriod.haarMeasure.map (D.linkFamily eL) =
      PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)
def ActionAgrees (eL : D.cubicPeriod.DirectedEdge ≃ D.PeriodicLink)
    (eP : D.cubicPeriod.Face ≃ D.PeriodicPlaquette) : Prop :=
  (∀ (U : D.cubicPeriod.GaugeConfig) (p : D.cubicPeriod.Face),
    (BoxTorus.faceHolonomy U p : Matrices.ComplexMatrix2) =
        PeriodicLattice.plaquetteHolonomy (D.linkFamily eL U) (eP p) ∧
      D.cubicPeriod.faceEnergy U p =
        PeriodicLattice.plaquetteCost (D.linkFamily eL U) (eP p)) ∧
    ∀ U : D.cubicPeriod.GaugeConfig,
      D.cubicPeriod.wilsonAction U = PeriodicLattice.wilsonAction (D.linkFamily eL U)
def LiftAgrees (eL : D.cubicPeriod.DirectedEdge ≃ D.PeriodicLink) : Prop :=
  (∀ b : D.Link, eL (D.cubicPeriod.projEdge b) = D.projLink b) ∧
    ∀ (U : D.cubicPeriod.GaugeConfig) (b : D.Link),
      (D.liftField (D.linkFamily eL U)) b = D.cubicPeriod.liftField U b
def CubicPeriodMatches : Prop :=
  D.CubicPeriodIsPeriodSubgroup ∧
    ∃ (e : D.cubicPeriod.TorusSpace ≃+ D.Torus) (eL : D.cubicPeriod.DirectedEdge ≃ D.PeriodicLink)
      (eP : D.cubicPeriod.Face ≃ D.PeriodicPlaquette),
      D.TorusEquiv e ∧ D.LinkEquiv e eL ∧ D.PlaquetteEquiv e eP ∧
        D.FieldEquiv eL ∧ D.ActionAgrees eL eP ∧
        D.LiftAgrees eL
def LatticeSymGroupLaws : Prop :=
  ∀ r r' : D.LatticeSym,
    (∃ c : D.LatticeSym, c.toFun = r.toFun ∘ r'.toFun ∧
      (∀ U : D.GaugeField,
        r'.pullbackField (r.pullbackField U) = c.pullbackField U) ∧
      ∀ F : D.GaugeField → ℂ, r.actOn (r'.actOn F) = c.actOn F) ∧
    ∃ i : D.LatticeSym, i.toFun ∘ r.toFun = id ∧ r.toFun ∘ i.toFun = id ∧
      ∃ h : D.GaugeField ≃ₜ D.GaugeField,
        ⇑h = r.pullbackField ∧ ⇑h.symm = i.pullbackField
end ChessboardSetup
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def cellsPerTorusSide : ℤ := 2 * (D.L : ℤ) ^ (((D.m : ℕ) : ℤ) - g.q).toNat
def blockIndices (k : Fin 4 → ℤ) : Set (Fin 4 → ℤ) :=
  {j | ∀ μ, k μ ≤ j μ ∧ j μ ≤ k μ + g.cellsPerTorusSide - 1}
def RatioAndPeriods : Prop :=
  g.cellSide / D.mesh = (g.cellRatio : ℝ) ∧ (g.cellRatio : ℝ) = (D.L : ℝ) ^ (g.q + ((D.K : ℕ) : ℤ)) ∧
    2 ≤ g.cellRatio ∧ (∃ z : ℤ, g.cellSide = (z : ℝ) * D.mesh) ∧
    ∀ (n : Fin 4 → ℤ) (hn : ∀ μ, 2 ≤ n μ),
      (g.boxPeriods n hn).subgroup =
          BoxTorus.periods (fun μ => (n μ : ℝ) * g.cellSide) ∧
        ∀ μ, (g.boxPeriods n hn).mult μ = n μ * g.cellRatio ∧ 4 ≤ n μ * g.cellRatio
def TorusSideCells : Prop :=
  g.q ≤ ((D.m : ℕ) : ℤ) ∧ g.cellsAcross = (g.cellsPerTorusSide : ℝ) ∧
    Even g.cellsPerTorusSide ∧
    ∃ hn : 2 ≤ g.cellsPerTorusSide,
      g.boxPeriods (fun _ => g.cellsPerTorusSide) (fun _ => hn) = D.cubicPeriod ∧
      ∀ W : AmbientSpace → ℂ, (∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) →
        (∀ x, ∀ v ∈ D.cubicPeriod.subgroup, W (x + v) = W x) →
        (g.boxPeriods (fun _ => g.cellsPerTorusSide) (fun _ => hn)).weightedPartition W =
          D.partitionFunctionOfPeriodic W
def BlockEqUnionCells (k : Fin 4 → ℤ) : Prop :=
  g.block k = ⋃ j ∈ g.blockIndices k, g.cell j ∧
    g.cellsWithin (g.block k) = g.cell '' g.blockIndices k ∧
    ((g.cell '' g.blockIndices k).ncard : ℤ) = g.cellsPerTorusSide ^ 4
end ReflectionGrid
def ReflectionGridArithmetic.Statement : Prop :=
  ∀ D : ChessboardSetup,
    D.CubicPeriodMatches ∧ D.LatticeSymGroupLaws ∧
    (∃ g : ReflectionGrid D, g.cellSide = (D.L : ℝ) * D.mesh ∧
      g.origin = (D.mesh / 2) • ∑ μ, coordVec μ) ∧
    ∀ g : ReflectionGrid D, g.RatioAndPeriods ∧
      (2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
        g.TorusSideCells ∧ ∀ k : Fin 4 → ℤ, g.BlockEqUnionCells k)
end ChessboardTori
end YangMills.Construction
end
