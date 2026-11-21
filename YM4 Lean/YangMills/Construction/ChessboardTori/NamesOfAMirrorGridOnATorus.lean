import YangMills.Construction.ChessboardTori.PeriodisationAndInducedMaps
import YangMills.Construction.Lattice.BlocksAndCorridors
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ChessboardSetup
variable (D : ChessboardSetup)
def periodicExpectation (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) : ℂ :=
  PeriodicLattice.gibbsExpectation D.L D.m D.K D.β F
def imageLink (s : D.Torus → D.Torus) (e : D.PeriodicLink) : D.PeriodicLink :=
  Classical.epsilon fun e' : D.PeriodicLink =>
    (e'.source : D.Torus) = s e.source ∧ (e'.target : D.Torus) = s e.target
def pullbackField (s : D.Torus → D.Torus) (V : D.PeriodicLink → Matrices.ComplexMatrix2) :
    D.PeriodicLink → Matrices.ComplexMatrix2 :=
  fun e => V (D.imageLink s e)
def pullbackObservable (s : D.Torus → D.Torus)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
  F ∘ D.pullbackField s
def liftedObservable (H : D.GaugeField → ℂ) :
    (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
  fun V => H (D.liftField V)
end ChessboardSetup
namespace ReflectionGrid
variable {D : ChessboardSetup} (G : ReflectionGrid D)
def torusWall (i : Fin 4) (j : ℤ) : Set D.Torus := D.proj '' G.wall i j
def torusWallFamily : Set (Set D.Torus) := range fun w : Fin 4 × ℤ => G.torusWall w.1 w.2
def liftCell (C : Set D.Torus) : Set AmbientSpace :=
  Classical.epsilon fun S : Set AmbientSpace => S ∈ G.cellSet ∧ D.proj '' S = C
def torusCellInterior (C : Set D.Torus) : Set D.Torus := D.proj '' interior (G.liftCell C)
def inducingElement (s : D.Torus → D.Torus) : G.reflectionGroup :=
  Classical.epsilon fun r : G.reflectionGroup => D.proj ∘ r.1 = s ∘ D.proj
def torusSign (s : D.Torus → D.Torus) : ℤˣ := orientationSign (G.inducingElement s).1
def torusCellLinks (C : Set D.Torus) : Set D.PeriodicLink :=
  {e | (e.source : D.Torus) ∈ G.torusCellInterior C ∧ (e.target : D.Torus) ∈ G.torusCellInterior C}
def torusCellRestrict (C : Set D.Torus)
    (V : PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ)) :
    G.torusCellLinks C → Conventions.StandingParameters.gaugeGroup :=
  fun e => ⟨V.1 e.1, V.2.1 e.1 (mem_univ _)⟩
def torusCellObservables (C : Set D.Torus) :
    Set ((D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :=
  {F | ∃ f : (G.torusCellLinks C → Conventions.StandingParameters.gaugeGroup) → ℂ,
    Measurable f ∧ (∃ c : ℝ, ∀ u, ‖f u‖ ≤ c) ∧
      ∀ V : PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ),
        F V.1 = f (G.torusCellRestrict C V)}
def torusTransport (s : D.Torus → D.Torus)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
  Conventions.signedConjFun (G.torusSign s) (D.pullbackObservable s F)
def torusCarrier (C C' : Set D.Torus) : D.Torus → D.Torus :=
  Classical.epsilon fun s : D.Torus → D.Torus => s ∈ G.inducedTorusMaps ∧ s '' C = C'
def torusTransportTo (C C' : Set D.Torus)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
  G.torusTransport (G.torusCarrier C C') F
def torusProduct (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
  fun V => ∏ᶠ s ∈ G.inducedTorusMaps, G.torusTransport s F V
def torusChessboardNorm (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) : ℝ :=
  ‖D.periodicExpectation (G.torusProduct F)‖ ^ (1 / G.cellsAcross ^ 4)
end ReflectionGrid
end ChessboardTori
end YangMills.Construction
end
