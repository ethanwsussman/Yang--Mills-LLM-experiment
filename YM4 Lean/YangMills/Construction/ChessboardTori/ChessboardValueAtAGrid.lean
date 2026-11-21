import YangMills.Construction.ChessboardTori.ChessboardEstimate
import YangMills.Construction.ChessboardTori.NamesOfAMirrorGridOnATorus
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
noncomputable section
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def ofRealFn (H : D.GaugeField → ℝ) : D.GaugeField → ℂ := fun U => (H U : ℂ)
def expOfReal (H : D.GaugeField → ℝ) : D.GaugeField → ℂ :=
  fun U => Complex.exp (H U : ℂ)
def liftedCopiesExpectation (S B : Set AmbientSpace) (F : D.GaugeField → ℂ) : ℂ :=
  D.periodicExpectation fun U =>
    ∏ᶠ S' ∈ g.cellsWithin B, D.liftedObservable (g.transportTo S S' F) U
def liftedProductExpectation (C : Set (Set AmbientSpace))
    (F : Set AmbientSpace → D.GaugeField → ℂ) : ℂ :=
  D.periodicExpectation (D.liftedObservable fun U => ∏ᶠ S ∈ C, F S U)
def liftedExpSumExpectation (S B : Set AmbientSpace) (H : D.GaugeField → ℝ) : ℂ :=
  D.periodicExpectation (D.liftedObservable fun U =>
    Complex.exp (∑ᶠ S' ∈ g.cellsWithin B, g.transportTo S S' (ofRealFn H) U))
end ReflectionGrid
def GridChessboardNorm.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ B ∈ g.blocks,
      (∀ S ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
        g.liftedCopiesExpectation S B F =
          ((g.chessboardNorm S F ^ (g.cellsAcross ^ 4) : ℝ) : ℂ)) ∧
      (∀ C ⊆ g.cellsWithin B, ∀ F : Set AmbientSpace → D.GaugeField → ℂ,
        (∀ S ∈ C, F S ∈ ReflectionGrid.cellObservables (D := D) S) →
          ‖ReflectionGrid.liftedProductExpectation (D := D) C F‖ ≤
            ∏ᶠ S ∈ C, g.chessboardNorm S (F S)) ∧
      (∀ S ∈ g.cellSet,
        (∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
          (∀ c : ℂ, g.chessboardNorm S (c • F) = ‖c‖ * g.chessboardNorm S F) ∧
          (∀ F' ∈ ReflectionGrid.cellObservables (D := D) S,
            g.chessboardNorm S (F + F') ≤ g.chessboardNorm S F + g.chessboardNorm S F') ∧
          (∀ S' ∈ g.cellSet, g.chessboardNorm S' (g.transportTo S S' F) = g.chessboardNorm S F) ∧
          g.chessboardNorm S (fun U => starRingEnd ℂ (F U)) = g.chessboardNorm S F ∧
          g.chessboardNorm S F ≤ InfiniteLattice.observableSupNorm F) ∧
        g.chessboardNorm S (fun _ => 1) = 1) ∧
      ∀ S ∈ g.cellSet, ∀ H : D.GaugeField → ℝ,
        ReflectionGrid.ofRealFn H ∈ ReflectionGrid.cellObservables (D := D) S →
          ReflectionGrid.expOfReal H ∈ ReflectionGrid.cellObservables (D := D) S ∧
          (∀ r : g.reflectionGroup,
            g.transportTo S (r.1 '' S) (ReflectionGrid.ofRealFn H) =
              ReflectionGrid.ofRealFn ((g.toLatticeSym r).actOn H) ∧
            g.transportTo S (r.1 '' S) (ReflectionGrid.expOfReal H) =
              fun U => Complex.exp (g.transportTo S (r.1 '' S) (ReflectionGrid.ofRealFn H) U)) ∧
          ((g.chessboardNorm S (ReflectionGrid.expOfReal H) ^ (g.cellsAcross ^ 4) : ℝ) : ℂ) =
            g.liftedExpSumExpectation S B H ∧
          Real.exp (-InfiniteLattice.observableSupNorm (ReflectionGrid.ofRealFn H)) ≤
            g.chessboardNorm S (ReflectionGrid.expOfReal H) ∧
          g.chessboardNorm S (ReflectionGrid.expOfReal H) ≤
            Real.exp (InfiniteLattice.observableSupNorm (ReflectionGrid.ofRealFn H))
end ChessboardTori
end
end YangMills.Construction
