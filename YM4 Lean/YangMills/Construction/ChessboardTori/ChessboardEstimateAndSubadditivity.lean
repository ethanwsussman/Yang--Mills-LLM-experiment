import YangMills.Construction.ChessboardTori.ChessboardSeminorm
import YangMills.Construction.ChessboardTori.MirrorPeriodicWeightsAsCellFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace CoupledGrid
variable (O : CoupledGrid)
def BlockExpectationsAndSeminormProperties
    (hside : 2 * O.cellSide ≤ PeriodicLattice.torusSide O.L O.m) : Prop :=
  ∀ (S : Set AmbientSpace) (hS : S ∈ O.grid.cellSet),
    (∃ h : (fun _ => 1) ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S,
      O.cellChessboardSeminorm hside hS ⟨_, h⟩ = 1) ∧
    ∀ F : ReflectionGrid.cellObservables (D := O.toChessboardSetup) S,
      (∀ B ∈ O.grid.blocks,
        ((O.grid.cellsWithin B).ncard : ℝ) = O.grid.cellsAcross ^ 4 ∧
        (O.grid.chessboardExpectation S B F).im = 0 ∧
        0 ≤ (O.grid.chessboardExpectation S B F).re ∧
        (∀ B' ∈ O.grid.blocks,
          O.grid.chessboardExpectation S B' F = O.grid.chessboardExpectation S B F) ∧
        (O.grid.chessboardExpectation S B F).re ^ (1 / O.grid.cellsAcross ^ 4) =
          O.cellChessboardSeminorm hside hS F) ∧
      (∀ (S' : Set AmbientSpace) (hS' : S' ∈ O.grid.cellSet),
        ∃ h : O.grid.transportTo S S' F ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S',
          O.cellChessboardSeminorm hside hS' ⟨_, h⟩ = O.cellChessboardSeminorm hside hS F) ∧
      (∃ h : (fun U => starRingEnd ℂ (F.1 U)) ∈
          ReflectionGrid.cellObservables (D := O.toChessboardSetup) S,
        O.cellChessboardSeminorm hside hS ⟨_, h⟩ = O.cellChessboardSeminorm hside hS F) ∧
      O.cellChessboardSeminorm hside hS F ≤ InfiniteLattice.observableSupNorm F.1 ∧
      (∀ ζ : ℂ, ∃ h : (fun U => ζ * F.1 U) ∈
          ReflectionGrid.cellObservables (D := O.toChessboardSetup) S,
        O.cellChessboardSeminorm hside hS ⟨_, h⟩ = ‖ζ‖ * O.cellChessboardSeminorm hside hS F) ∧
      ∀ F' : ReflectionGrid.cellObservables (D := O.toChessboardSetup) S,
        ∃ h : (fun U => F.1 U + F'.1 U) ∈
            ReflectionGrid.cellObservables (D := O.toChessboardSetup) S,
          O.cellChessboardSeminorm hside hS ⟨_, h⟩ ≤
            O.cellChessboardSeminorm hside hS F + O.cellChessboardSeminorm hside hS F'
def BlockProductExpectationBound
    (hside : 2 * O.cellSide ≤ PeriodicLattice.torusSide O.L O.m) : Prop :=
  ∀ B ∈ O.grid.blocks,
    ∀ F : (S : O.grid.cellsWithin B) → ReflectionGrid.cellObservables (D := O.toChessboardSetup) S.1,
      ‖O.toChessboardSetup.liftedExpectation fun U => ∏ᶠ S : O.grid.cellsWithin B, (F S).1 U‖ ≤
        ∏ᶠ S : O.grid.cellsWithin B, O.cellChessboardSeminorm hside S.2.1 (F S)
def SubadditivityAtSmallerSide (hside : 2 * O.cellSide ≤ PeriodicLattice.torusSide O.L O.m)
    (m' : ℕ+) : Prop :=
  (∀ W : AmbientSpace → ℂ, O.grid.IsReflectionPeriodic W →
    (O.toChessboardSetup.partitionFunctionOfPeriodic W).im = 0 ∧
    ((O.toChessboardSetup.withExponent m').partitionFunctionOfPeriodic W).im = 0 ∧
    0 ≤ (O.toChessboardSetup.partitionFunctionOfPeriodic W).re ∧
    (O.toChessboardSetup.partitionFunctionOfPeriodic W).re ≤
      ((O.toChessboardSetup.withExponent m').partitionFunctionOfPeriodic W).re ^
        ((PeriodicLattice.torusSide O.L O.m / PeriodicLattice.torusSide O.L m') ^ 4 : ℝ)) ∧
  (∀ (S : Set AmbientSpace) (hS : S ∈ O.grid.cellSet)
      (F : ReflectionGrid.cellObservables (D := O.toChessboardSetup) S),
    O.chessboardPartition S F = O.toChessboardSetup.partitionFunction 0 *
      ((O.cellChessboardSeminorm hside hS F ^ (O.grid.cellsAcross ^ 4) : ℝ) : ℂ) ∧
    (O.chessboardPartition S F).im = 0 ∧
    ((O.withExponent m').chessboardPartition S F.1).im = 0 ∧
    0 ≤ (O.chessboardPartition S F).re ∧
    (O.chessboardPartition S F).re ≤
      ((O.withExponent m').chessboardPartition S F.1).re ^
        ((PeriodicLattice.torusSide O.L O.m / PeriodicLattice.torusSide O.L m') ^ 4 : ℝ)) ∧
  ∀ W : AmbientSpace → ℂ, O.grid.IsReflectionPeriodic W → ∀ S ∈ O.grid.cellSet,
    O.cellExpWeight W S ∈ ReflectionGrid.cellObservables (D := O.toChessboardSetup) S ∧
    O.chessboardPartition S (O.cellExpWeight W S) =
      O.toChessboardSetup.partitionFunctionOfPeriodic W
end CoupledGrid
def ChessboardEstimateAndSubadditivity.Statement : Prop :=
  ∀ (O : CoupledGrid) (hside : 2 * O.cellSide ≤ PeriodicLattice.torusSide O.L O.m),
    O.BlockExpectationsAndSeminormProperties hside ∧
    O.BlockProductExpectationBound hside ∧
    ∀ m' : ℕ+, PeriodicLattice.torusSide O.L m' ≤ PeriodicLattice.torusSide O.L O.m →
      2 * O.cellSide ≤ PeriodicLattice.torusSide O.L m' → O.SubadditivityAtSmallerSide hside m'
end ChessboardTori
end YangMills.Construction
end
