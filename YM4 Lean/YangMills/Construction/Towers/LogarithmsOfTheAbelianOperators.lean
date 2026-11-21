import YangMills.Construction.Towers.LogarithmsSectorsAndDensityDefs
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
def AbelianOperatorLogarithms : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ z : ℝ, 0 < z →
    ∀ θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ, DensityDefined (L := L) z θ →
      AbelianLogDecomposition (vertexTensor (L := L)) (vertexPos L) z
          (laplacianOp θ) ∧
        AbelianLogDecomposition (edgeTensor (L := L)) (edgePos L) z
          (massiveOp θ)
end YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition
end
