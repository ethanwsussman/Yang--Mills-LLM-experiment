import YangMills.Construction.ChessboardTori.GridElementaryProperties
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ChessboardTori
def TorusReflectionGroup.Statement : Prop :=
  ∀ (D : ChessboardSetup) (g : ReflectionGrid D),
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m → g.TorusGroupQuotient
end YangMills.Construction.ChessboardTori
end
