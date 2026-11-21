import YangMills.Construction.Towers.TheUnitLatticeGivesIndexedSpaces
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.AbelianFieldDensity YangMills.Construction.Tower.LocalFamilies
open YangMills.Construction.OneLoopNotation
noncomputable section
namespace YangMills.Construction.Tower.LocalFamilies
def AbelianOperatorsLocallySmooth : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    IsLocallySmoothFamily (vertexPos L) (positiveEdgeInitial (L := L)) C (laplacianOp (L := L)) ∧
      IsLocallySmoothFamily (edgePos L) (positiveEdgeInitial (L := L)) C
        (AbelianFieldDensity.massiveOp (L := L))
end YangMills.Construction.Tower.LocalFamilies
end
