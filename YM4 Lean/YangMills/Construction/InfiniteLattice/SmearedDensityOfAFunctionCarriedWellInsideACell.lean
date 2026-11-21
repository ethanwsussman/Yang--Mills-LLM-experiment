import YangMills.Construction.SourcesAndGluing.GridsMirrorGridsCellAlgebrasAndTheChessboardValue
import Mathlib
import YangMills.Construction.ChessboardTori.ChessboardValueWhereTheSideVaries
import YangMills.Construction.InfiniteLattice.MirrorGridsCopiesAndChessboardValuesOfMultipleReflections
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def signedCopyOnTorus {D : GluingSetup} (r : Equiv.Perm D.Torus)
    (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
  Conventions.signedConjFun (orientationSign r) (PeriodicLattice.transportObservable r F)
namespace CubicGrid
variable {D : GluingSetup} (g : CubicGrid D)
def reflectionProductOnTorus (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) :
    (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ :=
  fun U => ∏ᶠ r : g.reflectionGroup, signedCopyOnTorus (r : Equiv.Perm D.Torus) F U
def chessboardNormOnTorus (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) : ℝ :=
  ‖D.expectation (g.reflectionProductOnTorus F)‖ ^ (1 / D.cellCount g.edge ^ 4)
theorem chessboardNormOnTorus_pullToTorus (F : D.GridField → ℂ) :
    g.chessboardNormOnTorus (D.pullToTorus F) = g.chessboardNorm F :=
  rfl
end CubicGrid
end YangMills.Construction.SourcesAndGluing
end
end

noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
namespace MultipleReflections
namespace Setup
variable (D : Setup)
def proj : AmbientSpace → D.Torus :=
  ChessboardTori.ChessboardSetup.proj ⟨D.toStandingParameters, D.β, D.β_pos⟩
def expSmeared (φ : AmbientSpace → ℝ) (z c : ℂ) : D.GaugeField → ℂ :=
  fun U => Complex.exp (z * ((InfiniteLattice.smearedEnergy φ U : ℝ) : ℂ) - c)
def torusExpSmeared (ψ : D.Torus → ℝ) (z c : ℂ) :
    (PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ) → Matrices.ComplexMatrix2) → ℂ :=
  fun U => Complex.exp (z * ((PeriodicLattice.smearedObservable ψ U : ℝ) : ℂ) - c)
end Setup
def SmearedEnergyWellInsideTile.Statement : Prop :=
  ∀ (D : Setup) (G : D.Grid) (k : Fin 4 → ℤ) (φ : AmbientSpace → ℝ),
    Measurable φ → TestFunctions.IsBoundedFun φ →
    (∀ x, x ∉ TestFunctions.closedBallR4 (G.tileCenter k) (G.edge / 4) → φ x = 0) →
    (∀ p : InfiniteLattice.ElementaryPlaquette D.mesh,
      p.center ∈ TestFunctions.closedBallR4 (G.tileCenter k) (G.edge / 4) →
        ∀ y ∈ p.cornerSet, (y : AmbientSpace) ∈ G.tileInterior k) ∧
    (fun U : D.GaugeField => ((InfiniteLattice.smearedEnergy φ U : ℝ) : ℂ)) ∈ G.tileAlgebra k ∧
    (∀ z c : ℂ, D.expSmeared φ z c ∈ G.tileAlgebra k) ∧
    (2 * G.edge ≤ D.side → TestFunctions.IsLipschitzFor TestFunctions.euclidDistR4 φ →
      ∀ M : ℝ, 0 < M →
        TestFunctions.IsPeriodizable (PeriodicLattice.torusSide D.L D.m)
          (TestFunctions.closedBallR4 (G.tileCenter k) (G.edge / 4)) φ ∧
        TestFunctions.IsLipschitzFor TestFunctions.euclidDistTorus
          (TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) φ) ∧
        (∀ y, y ∉ TestFunctions.closedBallTorus (D.proj (G.tileCenter k)) (G.edge / 4) →
          TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) φ y = 0) ∧
        TestFunctions.sharpNormTorus M (TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) φ) ≤
          TestFunctions.sharpNormR4 M φ ∧
        ∀ z c : ℂ,
          (∀ U : D.TorusField,
            D.pullbackObs (D.expSmeared φ z c) U =
              D.torusExpSmeared
                (TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) φ) z c U.1) ∧
          (∃ g : ChessboardTori.ReflectionGrid ⟨D.toStandingParameters, D.β, D.β_pos⟩,
            g.cellSide = G.edge ∧ g.origin = G.shift ∧
            ∃ (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m)
              (hC : D.proj '' G.tile k ∈ g.torusCellSet)
              (hF : D.torusExpSmeared
                  (TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) φ) z c ∈
                g.torusCellObservables (D.proj '' G.tile k)),
              G.chessboardNorm k (D.expSmeared φ z c) =
                g.torusChessboardNormAtSide hside hC _ hF) ∧
          ∀ i : ℕ, ∃ g : SourcesAndGluing.CubicGrid ⟨D.toStandingParameters, D.β, D.β_pos, i⟩,
            g.edge = G.edge ∧ g.origin = G.shift ∧
            G.chessboardNorm k (D.expSmeared φ z c) =
              g.chessboardNormOnTorus
                (D.torusExpSmeared
                  (TestFunctions.periodize (PeriodicLattice.torusSide D.L D.m) φ) z c))
end MultipleReflections
end YangMills.Construction
end
