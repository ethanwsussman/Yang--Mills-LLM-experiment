import YangMills.Construction.Towers.LogarithmsSectorsAndDensityDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
open UnitLatticeL2 (vertexPos edgePos)
def UnitLatticeTraceSplits.Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    TraceSplitsBySector (vertexTensor (L := L)) (vertexPos L) ∧
      TraceSplitsBySector (edgeTensor (L := L)) (edgePos L)
end YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
end
