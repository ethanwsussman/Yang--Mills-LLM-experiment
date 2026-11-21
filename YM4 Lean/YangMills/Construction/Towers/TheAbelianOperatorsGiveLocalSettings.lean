import YangMills.Construction.Towers.TheUnitLatticeGivesIndexedSpaces
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.AbelianFieldDensity YangMills.Construction.Tower.LocalFamilies
open YangMills.Construction.OneLoopNotation
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
def AbelianOperatorsLocalExpansion : Prop :=
  ∀ z : ℝ, 0 < z → ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    IsLocalExpansionSetting (vertexPos L) (positiveEdgeInitial (L := L)) 3 4 z C (laplacianOp (L := L)) ∧
      IsLocalExpansionSetting (edgePos L) (positiveEdgeInitial (L := L)) 12 4 z C
        (AbelianFieldDensity.massiveOp (L := L))
end YangMills.Construction.Tower.LocalFamilies
end
