import YangMills.Construction.Towers.LogarithmsSectorsAndDensityDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower.UnitLatticeL2
namespace Tower.AbelianFieldDensity.SectorDecomposition
def DensityPreservationGivesInvariance : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z → ∀ n : Fin 4 → ℤ,
    ∀ (Vs : L2Field (FullSpace.Vertex L 0 0) → L2Field (FullSpace.Vertex L 0 0))
      (Vb : L2Field (PeriodicOperators.PosEdge L 0 0) → L2Field (PeriodicOperators.PosEdge L 0 0)),
      PreservesTraceDensity (L := L) (vertexPos L) Vs n →
      PreservesTraceDensity (L := L) (edgePos L) Vb n →
      DensityInvariance z Vs Vb n
end Tower.AbelianFieldDensity.SectorDecomposition
end YangMills.Construction
end
