import YangMills.Construction.Towers.OperatorsDependingLocallyOnAField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
open UnitLatticeL2
def positiveEdgeInitial {L : ℕ} (e : FullSpace.PositiveEdge (meshAt L 0 0)) : InfiniteLattice.AmbientSpace :=
  (e.1.initial : InfiniteLattice.AmbientSpace)
def UnitLatticeIndexedSpaces : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z C : ℝ, 0 < z → 0 < C →
    IsIndexedL2Space (vertexPos L) 3 z C ∧ IsIndexedL2Space (edgePos L) 12 z C ∧
      IsIntegerPlacement (positiveEdgeInitial (L := L)) 4
end YangMills.Construction.Tower.LocalFamilies
end
