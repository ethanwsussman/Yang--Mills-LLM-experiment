import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace ReflectionGrid
variable {D : ChessboardSetup} (g : ReflectionGrid D)
def productOfTransports (S B : Set AmbientSpace) (F : D.GaugeField → ℂ) : D.GaugeField → ℂ :=
  fun U => ∏ᶠ S' ∈ g.cellsWithin B, g.transportTo S S' F U
def chessboardExpectation (S B : Set AmbientSpace) (F : D.GaugeField → ℂ) : ℂ :=
  D.liftedExpectation (g.productOfTransports S B F)
def chessboardNorm (S : Set AmbientSpace) (F : D.GaugeField → ℂ) : ℝ :=
  (g.chessboardExpectation S (g.block 0) F).re ^ (1 / g.cellsAcross ^ 4)
def reflectedSourceTerm (f : AmbientSpace → ℂ) (r : g.reflectionGroup) (x : AmbientSpace) : ℂ :=
  Conventions.signedConj (orientationSign r.1) (f (r.1⁻¹ x))
def periodizedSource (f : AmbientSpace → ℂ) (x : AmbientSpace) : ℂ :=
  ∑ᶠ r : g.reflectionGroup, g.reflectedSourceTerm f r x
end ReflectionGrid
def ChessboardInequality.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    (∀ B ∈ g.blocks, ∀ S ∈ g.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
      (g.chessboardExpectation S B F).im = 0 ∧ 0 ≤ (g.chessboardExpectation S B F).re ∧
        ∀ B' ∈ g.blocks, g.chessboardExpectation S B' F = g.chessboardExpectation S B F) ∧
    (∀ B ∈ g.blocks, ∀ F : Set AmbientSpace → D.GaugeField → ℂ,
      (∀ S ∈ g.cellsWithin B, F S ∈ ReflectionGrid.cellObservables (D := D) S) →
        ‖D.liftedExpectation fun U => ∏ᶠ S ∈ g.cellsWithin B, F S U‖ ≤
          ∏ᶠ S ∈ g.cellsWithin B, g.chessboardNorm S (F S)) ∧
    (∀ S ∈ g.cellSet,
      (∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
        (∀ S' ∈ g.cellSet, g.chessboardNorm S' (g.transportTo S S' F) = g.chessboardNorm S F) ∧
        g.chessboardNorm S F = g.chessboardNorm S (fun U => starRingEnd ℂ (F U)) ∧
        g.chessboardNorm S F ≤ InfiniteLattice.observableSupNorm F) ∧
      g.chessboardNorm S (fun _ => 1) = 1) ∧
    ∀ S ∈ g.cellSet, ∀ (f : AmbientSpace → ℂ) (Q : Set AmbientSpace), (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
      (∀ x, x ∉ Q → f x = 0) → IsCompact Q → Q ⊆ interior S →
      (∀ x ∈ Q, ∀ y ∈ g.walls, 1 ≤ TorusMetric.euclidNormVec (x - y)) →
      (fun U => Complex.exp (D.smeared f U)) ∈ ReflectionGrid.cellObservables (D := D) S ∧
      (∀ x, {r : g.reflectionGroup | g.reflectedSourceTerm f r x ≠ 0}.Subsingleton) ∧
      g.IsReflectionPeriodic (g.periodizedSource f) ∧
      (∀ (x : AmbientSpace) (k : Fin 4 → ℤ), g.periodizedSource f
        (x + TestFunctions.latticeTranslate (PeriodicLattice.torusSide D.L D.m) k) = g.periodizedSource f x) ∧
      ((g.chessboardNorm S (fun U => Complex.exp (D.smeared f U)) ^ (g.cellsAcross ^ 4) : ℝ) : ℂ) =
        D.partitionFunctionOfPeriodic (g.periodizedSource f) / D.partitionFunction 0
end ChessboardTori
end YangMills.Construction
end
