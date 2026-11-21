import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ChessboardTori
def ChessboardExpectationRules.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ B ∈ g.blocks, ∀ S ∈ g.cellSet,
      (∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
        (∀ S' ∈ g.cellSet,
          D.liftedExpectation (fun U => ∏ᶠ T ∈ g.cellsWithin B, g.transportTo S' T (g.transportTo S S' F) U) =
            D.liftedExpectation fun U => ∏ᶠ T ∈ g.cellsWithin B, g.transportTo S T F U) ∧
        D.liftedExpectation
            (fun U => ∏ᶠ T ∈ g.cellsWithin B, g.transportTo S T (fun V => starRingEnd ℂ (F V)) U) =
          starRingEnd ℂ (D.liftedExpectation fun U => ∏ᶠ T ∈ g.cellsWithin B, g.transportTo S T F U) ∧
        ‖D.liftedExpectation fun U => ∏ᶠ T ∈ g.cellsWithin B, g.transportTo S T F U‖ ≤
          InfiniteLattice.observableSupNorm F ^ (g.cellsWithin B).ncard) ∧
      D.liftedExpectation (fun U => ∏ᶠ T ∈ g.cellsWithin B, g.transportTo S T (fun _ => 1) U) = 1
end ChessboardTori
end YangMills.Construction
end
