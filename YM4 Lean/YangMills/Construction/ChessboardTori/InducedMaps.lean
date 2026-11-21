import YangMills.Construction.ChessboardTori.NamesOfAMirrorGridOnATorus
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
def IsCoordDiagonal (R : AmbientSpace →ₗ[ℝ] AmbientSpace) : Prop :=
  ∀ μ, ∃ c : ℝ, R (coordVec μ) = c • coordVec μ
namespace PeriodSubgroup
variable {D : ChessboardSetup} (P : PeriodSubgroup D)
def IsStableUnder (r : D.LatticeSym) : Prop :=
  linearComponent r.toFun '' (P.subgroup : Set AmbientSpace) = P.subgroup
def quotientMap (r : D.LatticeSym) : P.TorusSpace → P.TorusSpace :=
  haveI : Nonempty (P.TorusSpace → P.TorusSpace) := ⟨id⟩
  Classical.epsilon (P.InducesMap r)
def HasInverseQuotientMaps (r : D.LatticeSym) : Prop :=
  P.InducesMap r (P.quotientMap r) ∧
    ∃ r' : D.LatticeSym, (∀ x, r'.toFun (r.toFun x) = x) ∧ (∀ x, r.toFun (r'.toFun x) = x) ∧
      P.InducesMap r' (P.quotientMap r') ∧
      P.quotientMap r ∘ P.quotientMap r' = id ∧ P.quotientMap r' ∘ P.quotientMap r = id
def RespectsLatticeStructure (s : P.TorusSpace → P.TorusSpace) : Prop :=
  P.IsTorusIsometry s ∧
    s '' (P.gridSubgroup : Set P.TorusSpace) = P.gridSubgroup ∧
    (∀ e : P.DirectedEdge, ((P.mapEdge s e).source : P.TorusSpace) = s e.source ∧
      ((P.mapEdge s e).target : P.TorusSpace) = s e.target) ∧
    Function.Bijective (P.mapEdge s) ∧
    (∀ e : P.DirectedEdge, P.mapEdge s e.flip = (P.mapEdge s e).flip) ∧
    (∀ f : P.Face, (fun x : P.GridPoint => (x : P.TorusSpace)) '' (P.mapFace s f).vertexSet =
      s '' ((fun x : P.GridPoint => (x : P.TorusSpace)) '' f.vertexSet)) ∧
    Function.Bijective (P.mapFace s) ∧
    ∀ f : P.Face, P.faceCenter (P.mapFace s f) = s (P.faceCenter f)
def QuotientMapsCompose (r r' : D.LatticeSym) : Prop :=
  (∃ r'' : D.LatticeSym, r''.toFun = r.toFun ∘ r'.toFun ∧
    P.InducesMap r'' (P.quotientMap r ∘ P.quotientMap r')) ∧
    (∀ U : P.GaugeConfig, P.pullback (P.quotientMap r') (P.pullback (P.quotientMap r) U) =
      P.pullback (P.quotientMap r ∘ P.quotientMap r') U) ∧
    ∀ F : P.GaugeConfig → ℂ, P.precompose (P.quotientMap r) (P.precompose (P.quotientMap r') F) =
      P.precompose (P.quotientMap r ∘ P.quotientMap r') F
def PullbackCompatible (r : D.LatticeSym) : Prop :=
  ∀ U : P.GaugeConfig,
    (∀ e : P.DirectedEdge, BoxTorus.edgeVariable (P.pullback (P.quotientMap r) U) e =
      BoxTorus.edgeVariable U (P.mapEdge (P.quotientMap r) e)) ∧
    (∀ e : D.Link, P.liftField U (r.linkMap e) =
      P.liftField (P.pullback (P.quotientMap r) U) e) ∧
    ∀ f : P.Face, P.faceEnergy (P.pullback (P.quotientMap r) U) f =
      P.faceEnergy U (P.mapFace (P.quotientMap r) f)
def PullbackPreservesHaarAndAction (s : P.TorusSpace → P.TorusSpace) : Prop :=
  (∃ h : P.GaugeConfig ≃ₜ P.GaugeConfig, ⇑h = P.pullback s) ∧
    MeasurePreserving (P.pullback s) P.haarMeasure P.haarMeasure ∧
    ∀ U : P.GaugeConfig, P.wilsonAction (P.pullback s U) = P.wilsonAction U
end PeriodSubgroup
def ChessboardSetup.PreservesPeriodicExpectation (D : ChessboardSetup) (r : D.LatticeSym) : Prop :=
  ∃ s : D.Torus → D.Torus, D.proj ∘ r.toFun = s ∘ D.proj ∧
    ∀ F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ, InfiniteLattice.IsPeriodicObservable F →
      D.periodicExpectation (D.pullbackObservable s F) = D.periodicExpectation F
def QuotientMapsStatement : Prop :=
  ∀ D : ChessboardSetup,
    (∀ (P : PeriodSubgroup D) (r : D.LatticeSym), P.IsStableUnder r →
      P.HasInverseQuotientMaps r ∧ P.RespectsLatticeStructure (P.quotientMap r) ∧
        (∀ r' : D.LatticeSym, P.IsStableUnder r' → P.QuotientMapsCompose r r') ∧
        P.PullbackCompatible r ∧ P.PullbackPreservesHaarAndAction (P.quotientMap r)) ∧
    (∀ r : D.LatticeSym, D.cubicPeriod.IsStableUnder r → D.PreservesPeriodicExpectation r) ∧
    (∀ (P : PeriodSubgroup D) (r : D.LatticeSym), IsCoordDiagonal (linearComponent r.toFun) →
      P.IsStableUnder r) ∧
    (∀ r : D.LatticeSym, D.cubicPeriod.IsStableUnder r) ∧
    ∀ s : PeriodicLattice.TorusLatticeSymmetry D.L D.m (D.K : ℕ),
      ∃ r : D.LatticeSym, D.proj ∘ r.toFun = s.toFun ∘ D.proj
end YangMills.Construction.ChessboardTori
end
