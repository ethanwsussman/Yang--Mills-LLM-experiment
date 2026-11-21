import YangMills.Construction.ChessboardTori.ChessboardIntegral
import YangMills.Construction.ChessboardTori.SubadditivityOfPartitionFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
open YangMills.Construction.InfiniteLattice (AmbientSpace)
namespace EvenIndexVector
def stretch (n : EvenIndexVector) (μ : Fin 4) {j : ℕ} (hj : 1 ≤ j) : EvenIndexVector where
  coord := scaleCoord n.coord μ j
  two_le := two_le_scaleCoord n.two_le μ hj
  even κ := by
    by_cases h : κ = μ
    · subst h
      simpa only [scaleCoord, Function.update_self] using (n.even κ).mul_left (j : ℤ)
    · simpa only [scaleCoord, Function.update_of_ne h] using n.even κ
end EvenIndexVector
def TorusStretchBound.Statement : Prop :=
  ∀ (O : CoupledGrid) (n : EvenIndexVector) (μ : Fin 4) (j : ℕ) (hj : 1 ≤ j),
    (∀ W : AmbientSpace → ℂ, O.grid.IsReflectionPeriodic W →
      ((O.periodSubgroupOf n).weightedPartition W).im = 0 ∧
      ((O.periodSubgroupOf (n.stretch μ hj)).weightedPartition W).im = 0 ∧
      0 ≤ ((O.periodSubgroupOf (n.stretch μ hj)).weightedPartition W).re ∧
      ((O.periodSubgroupOf (n.stretch μ hj)).weightedPartition W).re ≤
        ((O.periodSubgroupOf n).weightedPartition W).re ^ j) ∧
    ∀ C ∈ O.grid.cellSet, ∀ F ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) C,
      (O.chessboardPartitionOn n C F).im = 0 ∧
      (O.chessboardPartitionOn (n.stretch μ hj) C F).im = 0 ∧
      0 ≤ (O.chessboardPartitionOn (n.stretch μ hj) C F).re ∧
      (O.chessboardPartitionOn (n.stretch μ hj) C F).re ≤
        (O.chessboardPartitionOn n C F).re ^ j
end YangMills.Construction.ChessboardTori
end
