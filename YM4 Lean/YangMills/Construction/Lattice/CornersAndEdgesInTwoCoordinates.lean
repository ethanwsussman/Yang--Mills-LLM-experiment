import YangMills.Construction.Lattice.PartitionInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def CubeVertexEdgeAgreement : Prop :=
  ∀ (S : LevelUnitPartition) (Δ : Set S.Points), Δ ∈ S.cubes →
    (∀ v, PeriodicLattice.IsCubeVertex S.index v Δ ↔ S.IsCornerOf v Δ) ∧
      ∀ e, PeriodicLattice.IsCubeEdge S.index e Δ ↔ S.IsEdgeOf e Δ
end YangMills.Construction.PeriodicLattice
end
