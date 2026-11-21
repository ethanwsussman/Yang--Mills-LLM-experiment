import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
def ChessboardSetup.periodize (D : ChessboardSetup) (v : AmbientSpace → ℂ) (x : AmbientSpace) : ℂ :=
  ∑ᶠ k : Fin 4 → ℤ, v (x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k)
namespace PeriodSubgroup
variable {D : ChessboardSetup} (P : PeriodSubgroup D)
def IsTorusIsometry (r : P.TorusSpace → P.TorusSpace) : Prop :=
  ∀ u v, P.torusDist (r u) (r v) = P.torusDist u v
def InducesMap (r : D.LatticeSym) (r' : P.TorusSpace → P.TorusSpace) : Prop :=
  P.proj ∘ r.toFun = r' ∘ P.proj
instance : Nonempty P.DirectedEdge := ⟨P.projEdge (InfiniteLattice.Link.forwardFrom 0 0)⟩
instance : Nonempty P.Face := ⟨⟨0, 0, 1, by decide⟩⟩
def mapEdge (r' : P.TorusSpace → P.TorusSpace) (b : P.DirectedEdge) : P.DirectedEdge :=
  Classical.epsilon fun b' : P.DirectedEdge =>
    (b'.source : P.TorusSpace) = r' b.source ∧ (b'.target : P.TorusSpace) = r' b.target
def mapFace (r' : P.TorusSpace → P.TorusSpace) (p : P.Face) : P.Face :=
  Classical.epsilon fun p' : P.Face =>
    (fun x : P.GridPoint => (x : P.TorusSpace)) '' p'.vertexSet =
      r' '' ((fun x : P.GridPoint => (x : P.TorusSpace)) '' p.vertexSet)
def pullback (r' : P.TorusSpace → P.TorusSpace) (U : P.GaugeConfig) : P.GaugeConfig :=
  fun b => BoxTorus.edgeVariable U (P.mapEdge r' b.1)
def precompose (r' : P.TorusSpace → P.TorusSpace) (F : P.GaugeConfig → ℂ) : P.GaugeConfig → ℂ :=
  F ∘ P.pullback r'
end PeriodSubgroup
def ReflectionGrid.inducedTorusMaps {D : ChessboardSetup} (g : ReflectionGrid D) :
    Set (D.Torus → D.Torus) :=
  {r' | ∃ r ∈ g.reflectionGroup, D.proj ∘ r = r' ∘ D.proj}
end ChessboardTori
end YangMills.Construction
end
