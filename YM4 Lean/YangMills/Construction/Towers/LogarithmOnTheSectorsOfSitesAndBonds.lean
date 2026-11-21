import YangMills.Construction.Towers.LogarithmsSectorsAndDensityDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
def LogOnVertexAndEdgeSectors : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z →
    LogRestrictsToSector (vertexTensor (L := L)) z ∧ LogRestrictsToSector (edgeTensor (L := L)) z
end YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
end
