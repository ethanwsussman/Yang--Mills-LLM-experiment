import YangMills.Construction.Towers.LogarithmsSectorsAndDensityDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open UnitLatticeL2
namespace AbelianFieldDensity
open SectorDecomposition in
def GaugeKeepsTraceDensity : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ u ∈ FullSpace.gaugeGroupAt L 0 0,
    PreservesTraceDensity (L := L) (vertexPos L) (gaugeVertexFn (L := L) u) 0 ∧
      PreservesTraceDensity (L := L) (edgePos L) (gaugeEdgeFn (L := L) u) 0
end AbelianFieldDensity
end YangMills.Construction.Tower
end
