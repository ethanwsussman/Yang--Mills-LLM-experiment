import YangMills.Construction.InequalityOnMirroredCopies.TheInequalityOfACell
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open ChessboardTori
open InfiniteLattice (AmbientSpace)
def SmearedMemCellObservables : Prop :=
  ∀ (D : ChessboardSetup) (c : GridCell D) (ϱ : ℝ) (h : AmbientSpace → ℝ), SupportedInCell c ϱ h →
    ReflectionsAndOneInsertion.complexSmeared D h ∈ ReflectionGrid.cellObservables (D := D) c.cell
end YangMills.Construction.ReflectedCopies
end
