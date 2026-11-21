import YangMills.Construction.Towers.LogarithmsSectorsAndDensityDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
open UnitLatticeL2 (vertexPos edgePos)
open SectorDecomposition in
def UnitLatticeStarConj.Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    TraceStarConj (vertexTensor (L := L)) (vertexPos L) ∧
    TraceStarConj (edgeTensor (L := L)) (edgePos L)
end YangMills.Construction.Tower.AbelianFieldDensity
end
