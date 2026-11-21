import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGrids
import YangMills.Construction.ChessboardTori.CouplingAndGrid
import YangMills.Construction.ChessboardTori.GroupOfAGridAndCopies
import YangMills.Construction.ChessboardTori.InducedMaps
import YangMills.Construction.ChessboardTori.QuotientMapOnLinksAndPlaquettes
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace PeriodSubgroup
variable {D : ChessboardSetup} (P : PeriodSubgroup D)
def ProjCarriesEdgesAndFaces : Prop :=
  (P.subgroup : Set AmbientSpace) ⊆ D.gridPoints ∧
    (∀ e : D.Link, (P.projEdge e).source = P.projPoint e.initial ∧
      (P.projEdge e).target = P.projPoint e.terminal ∧
      ((P.projEdge e).IsForward ↔ e.IsPositivelyOriented)) ∧
    ∀ q : D.Plaquette, (P.projFace q).vertexSet = P.projPoint '' D.faceCorners q ∧
      P.faceCenter (P.projFace q) = P.proj q.center
def ProjSurjectiveOnCells : Prop :=
  Function.Surjective P.projPoint ∧
    (∀ f : P.DirectedEdge, f.IsForward → ∃ e : D.Link, e.IsPositivelyOriented ∧ P.projEdge e = f) ∧
    Function.Surjective P.projFace
def ProjFibersArePeriodOrbits : Prop :=
  (∀ x y : InfiniteLattice.LatticePoint D.mesh,
    P.projPoint x = P.projPoint y ↔ ∃ w ∈ D.periodSubgroupOfGrid P.mult, y = x + w) ∧
  (∀ e e' : D.Link, e.IsPositivelyOriented → e'.IsPositivelyOriented →
    (P.projEdge e = P.projEdge e' ↔ ∃ w ∈ D.periodSubgroupOfGrid P.mult, e' = D.shiftLink e w)) ∧
  ∀ q q' : D.Plaquette,
    P.projFace q = P.projFace q' ↔
      ∃ w ∈ D.periodSubgroupOfGrid P.mult, q' = D.shiftPlaquette q w
def EdgesAndCentersDetermine : Prop :=
  (∀ (x y : P.GridPoint) (κ κ' : Fin 4),
    BoxTorus.edgeFrom x κ = BoxTorus.edgeFrom y κ' → x = y ∧ κ = κ') ∧
  ∀ q q' : P.Face, P.faceCenter q = P.faceCenter q' →
    q.corner = q'.corner ∧ q.dir₁ = q'.dir₁ ∧ q.dir₂ = q'.dir₂ ∧ q = q'
def LiftIsPeriodicGaugeField : Prop :=
  (∀ U : P.GaugeConfig, P.LiftIsGaugeField U) ∧
    Continuous P.liftGaugeField ∧
    (∀ (U : P.GaugeConfig) (q : D.Plaquette),
      InfiniteLattice.faceEnergy (P.liftGaugeField U) q =
        P.faceEnergy U (P.projFace q)) ∧
    ∀ U : P.GaugeConfig, ∀ w ∈ D.periodSubgroupOfGrid P.mult,
      (InfiniteLattice.shift w).pullbackField (P.liftGaugeField U) =
        P.liftGaugeField U
def InducesUniqueQuotientMap (r : D.LatticeSym) : Prop :=
  (∃! s : P.TorusSpace → P.TorusSpace, P.InducesMap r s) ∧
    Function.Bijective (P.quotientMap r) ∧
    P.quotientMap r '' (P.gridSubgroup : Set P.TorusSpace) = P.gridSubgroup ∧
    (∀ q : P.Face,
      (fun x : P.GridPoint => (x : P.TorusSpace)) '' (P.mapFace (P.quotientMap r) q).vertexSet =
        P.quotientMap r '' ((fun x : P.GridPoint => (x : P.TorusSpace)) '' q.vertexSet)) ∧
    Function.Surjective (P.mapFace (P.quotientMap r)) ∧
    (∀ q : D.Plaquette, P.mapFace (P.quotientMap r) (P.projFace q) =
      P.projFace (D.imageFace r q)) ∧
    ∀ U : P.GaugeConfig,
      r.pullbackField (P.liftGaugeField U) =
          P.liftGaugeField (P.pullback (P.quotientMap r) U) ∧
        ∀ q : P.Face, P.faceEnergy (P.pullback (P.quotientMap r) U) q =
          P.faceEnergy U (P.mapFace (P.quotientMap r) q)
end PeriodSubgroup
namespace ChessboardSetup
variable (D : ChessboardSetup)
def EdgesAndCentersDetermine : Prop :=
  (∀ (x y : InfiniteLattice.LatticePoint D.mesh) (κ κ' : Fin 4),
    InfiniteLattice.Link.forwardFrom x κ = InfiniteLattice.Link.forwardFrom y κ' → x = y ∧ κ = κ') ∧
  ∀ q q' : D.Plaquette, q.center = q'.center →
    q.corner = q'.corner ∧ q.lowAxis = q'.lowAxis ∧ q.highAxis = q'.highAxis ∧ q = q'
def LiftedExpectationFormula : Prop :=
  ∀ F : D.GaugeField → ℂ, InfiniteLattice.IsBoundedObservable F →
    D.liftedExpectation F = (D.partitionFunction 0)⁻¹ *
      ∫ U, F (D.liftField U) *
        Complex.exp (-(D.β : ℂ) * (PeriodicLattice.wilsonAction U : ℂ))
        ∂PeriodicLattice.productHaarMeasure D.L D.m ((D.K : ℕ) : ℤ)
end ChessboardSetup
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def TransportIsPeriodic (P : PeriodSubgroup D) : Prop :=
  (P.subgroup : Set AmbientSpace) ⊆ BoxTorus.periods (fun _ => 2 * g.cellSide) ∧
    ∀ C ∈ g.cellSet, ∀ C' ∈ g.cellSet, ∀ F ∈ cellObservables (D := D) C, ∀ w ∈ D.periodSubgroupOfGrid P.mult,
      (fun x : AmbientSpace => x + (w : AmbientSpace)) '' C' ∈ g.cellSet ∧
        g.transportTo C ((fun x : AmbientSpace => x + (w : AmbientSpace)) '' C') F =
          (InfiniteLattice.shift w).actOn (g.transportTo C C' F) ∧
        ∀ U : P.GaugeConfig,
          g.transportTo C ((fun x : AmbientSpace => x + (w : AmbientSpace)) '' C') F (P.liftGaugeField U) =
            g.transportTo C C' F (P.liftGaugeField U)
def TransportThroughReflections (P : PeriodSubgroup D) : Prop :=
  ∀ C ∈ g.cellSet, ∀ F ∈ cellObservables (D := D) C, ∀ (μ : Fin 4) (k : ℤ),
    (g.transportTo C (g.reflect μ k '' C) F = fun U : D.GaugeField =>
      starRingEnd ℂ ((g.toLatticeSym (g.reflectElem μ k)).actOn F U)) ∧
    ∀ U : P.GaugeConfig,
      g.transportTo C (g.reflect μ k '' C) F (P.liftGaugeField U) =
        starRingEnd ℂ (F (P.liftGaugeField (P.pullback
          (P.quotientMap (g.toLatticeSym (g.reflectElem μ k))) U)))
end ReflectionGrid
def BoxTorusQuotient.Statement : Prop :=
  ∀ G : CoupledGrid,
    (∀ (T : Fin 4 → ℤ) (hT : ∀ κ, 2 ≤ T κ),
      (G.grid.boxPeriods T hT).ProjCarriesEdgesAndFaces ∧
      (G.grid.boxPeriods T hT).ProjSurjectiveOnCells ∧
      (G.grid.boxPeriods T hT).ProjFibersArePeriodOrbits ∧
      G.toChessboardSetup.EdgesAndCentersDetermine ∧
      (G.grid.boxPeriods T hT).EdgesAndCentersDetermine ∧
      (G.grid.boxPeriods T hT).LiftIsPeriodicGaugeField ∧
      (∀ r : G.grid.reflectionGroup,
        (G.grid.boxPeriods T hT).InducesUniqueQuotientMap (G.grid.toLatticeSym r)) ∧
      ((∀ κ, Even (T κ)) → G.grid.TransportIsPeriodic (G.grid.boxPeriods T hT)) ∧
      G.grid.TransportThroughReflections (G.grid.boxPeriods T hT)) ∧
    (2 * G.grid.cellSide ≤ PeriodicLattice.torusSide G.L G.m →
      G.grid.TorusSideCells ∧ G.toChessboardSetup.CubicPeriodMatches ∧
        G.toChessboardSetup.LiftedExpectationFormula)
end YangMills.Construction.ChessboardTori
end
