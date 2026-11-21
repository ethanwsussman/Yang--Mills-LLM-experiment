import YangMills.Construction.ChessboardTori.BoxWithAnOuterConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def BoxBoundaryCount.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D), g.IsCoarse →
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    ∀ B ∈ g.blocks,
      ((D.boundaryPlaquetteCount B + D.torusBoundaryPlaquetteCount B : ℕ) : ℝ) ≤
        (boxBoundaryConstant : ℝ) * (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3
end YangMills.Construction.ChessboardTori
end
