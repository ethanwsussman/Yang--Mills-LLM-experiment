import YangMills.Construction.ChessboardTori.ChessboardValueWhereTheSideVaries
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ChessboardTori
namespace ChessboardSetup
variable (D : ChessboardSetup)
def torusSupNorm (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ) : ℝ :=
  ⨆ U : PeriodicLattice.compactGaugeFields D.L D.m ((D.K : ℕ) : ℤ), ‖F U.1‖
end ChessboardSetup
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def PreservesLatticeAndWalls (r : D.Torus → D.Torus) : Prop :=
  (∀ u v, TorusMetric.torusEuclidNorm (r u - r v) = TorusMetric.torusEuclidNorm (u - v)) ∧
    r '' (PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ) : Set D.Torus) =
      PeriodicLattice.sublattice D.L D.m ((D.K : ℕ) : ℤ) ∧
    (fun P : Set D.Torus => r '' P) '' g.torusWallFamily = g.torusWallFamily
def torusCellsWithin (Q : Set D.Torus) : Set (Set D.Torus) := {C | C ∈ g.torusCellSet ∧ C ⊆ Q}
end ReflectionGrid
def ChessboardBoundOnReflectionGrids.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D)
    (hside : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m),
    (∀ (F : g.torusCellSet → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ)
      (hF : ∀ C, F C ∈ g.torusCellObservables C.1),
      ‖D.periodicExpectation fun U => ∏ᶠ C, F C U‖ ≤
        ∏ᶠ C, g.torusChessboardNormAtSide hside C.2 (F C) (hF C)) ∧
    (∀ (C : Set D.Torus) (hC : C ∈ g.torusCellSet)
      (F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ)
      (hF : F ∈ g.torusCellObservables C) (z : ℂ),
      g.torusChessboardNormAtSide hside hC F hF ≤ D.torusSupNorm F ∧
      (∃ h : (fun _ => 1) ∈ g.torusCellObservables C,
        g.torusChessboardNormAtSide hside hC (fun _ => 1) h = 1) ∧
      (∃ h : (fun U => z * F U) ∈ g.torusCellObservables C,
        g.torusChessboardNormAtSide hside hC (fun U => z * F U) h =
          ‖z‖ * g.torusChessboardNormAtSide hside hC F hF) ∧
      (∃ h : (fun U => starRingEnd ℂ (F U)) ∈ g.torusCellObservables C,
        g.torusChessboardNormAtSide hside hC (fun U => starRingEnd ℂ (F U)) h =
          g.torusChessboardNormAtSide hside hC F hF) ∧
      ∀ r : D.Torus → D.Torus, g.PreservesLatticeAndWalls r →
        ∃ (hrC : r '' C ∈ g.torusCellSet)
          (hrF : D.pullbackObservable r F ∈ g.torusCellObservables (r '' C)),
          (∃ σ : D.Torus ≃ D.Torus, ⇑σ = r ∧
            D.pullbackObservable r F = PeriodicLattice.transportObservable σ F) ∧
          g.torusChessboardNormAtSide hside hrC (D.pullbackObservable r F) hrF =
            g.torusChessboardNormAtSide hside hC F hF) ∧
    ∀ (k₀ : ℕ) (g' : ReflectionGrid D), g'.cellSide = (D.L : ℝ) ^ k₀ * g.cellSide →
      ∀ hside' : 2 * g'.cellSide ≤ PeriodicLattice.torusSide D.L D.m,
      (∀ (μ : Fin 4) (k : ℤ), ∃ (μ' : Fin 4) (k' : ℤ), g'.wall μ k = g.wall μ' k') →
      ∀ (Q : Set D.Torus) (hQ : Q ∈ g'.torusCellSet)
        (F : g.torusCellsWithin Q → (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ)
        (hF : ∀ C, F C ∈ g.torusCellObservables C.1),
        ∃ h : (fun U => ∏ᶠ C, F C U) ∈ g'.torusCellObservables Q,
          g'.torusChessboardNormAtSide hside' hQ (fun U => ∏ᶠ C, F C U) h ≤
            ∏ᶠ C, g.torusChessboardNormAtSide hside C.2.1 (F C) (hF C)
end YangMills.Construction.ChessboardTori
end
