import YangMills.Construction.ChessboardTori.GridsCellsAndCopies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def ChessboardBlockInvariance.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D),
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ B ∈ g.blocks, ∀ B' ∈ g.blocks, ∀ S ∈ g.cellSet,
      ∀ F ∈ ReflectionGrid.cellObservables (D := D) S,
        D.liftedExpectation (fun U => ∏ᶠ S' ∈ g.cellsWithin B', g.transportTo S S' F U) =
          D.liftedExpectation fun U => ∏ᶠ S' ∈ g.cellsWithin B, g.transportTo S S' F U
end YangMills.Construction.ChessboardTori
end
