import YangMills.Construction.MirrorGridsOfEverySide.PropertiesOfAMirrorGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ChessboardTori (ReflectionGrid)
namespace MirrorGridsAllSides
def AllGridsTorusActOnCellObservables : Prop :=
  ∀ (D : GridSetup) (g : ReflectionGrid D), g.HasAdmissibleSide →
    2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m →
    TorusActsOnCellObservables g
end MirrorGridsAllSides
end YangMills.Construction
end
