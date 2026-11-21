import YangMills.Construction.DirichletOperator.ScalesOfTheApproximateInverse
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open RegionSequence RegionSequence.NestedRegions PartitionCubes
namespace CellSources
variable {𝒮 : NestedRegions} {M : ℕ}
def termAtCell (Q : LevelCube 𝒮 M) (y : 𝒮.Point) (f : 𝒮.FineBond → ℝ) :
    Q.system.setting.FineBond → ℝ :=
  Q.system.pullBonds Q.partitionFn (cellCutBond y f)
structure CellDecomposition (Q : LevelCube 𝒮 M) (f : 𝒮.FineBond → ℝ) : Prop where
  centres_finite : 𝒮.allCentres.Finite
  mem_forms : ∀ y ∈ 𝒮.allCentres, termAtCell Q y f ∈ Q.system.forms
  sum_mem_forms : ∑ᶠ y ∈ 𝒮.allCentres, termAtCell Q y f ∈ Q.system.forms
  sum_eq : ∑ᶠ y ∈ 𝒮.allCentres, termAtCell Q y f = Q.system.pullBonds Q.partitionFn f
  inv_eq : Q.system.inv (Q.system.pullBonds Q.partitionFn f) =
    ∑ᶠ y ∈ 𝒮.allCentres, Q.system.inv (termAtCell Q y f)
  eq_zero_of_not_near : ∀ y ∈ 𝒮.allCentres, Q ∉ CubeGeometry.activeNear 𝒮 M y → termAtCell Q y f = 0
  supported : ∀ y ∈ 𝒮.allCentres, Q ∈ CubeGeometry.activeNear 𝒮 M y →
    AnchorSupported (𝒮 := Q.system.setting) (cubeHalfSide (Q.system.embed y) (𝒮.levelScale y))
      (termAtCell Q y f)
  sup_le : ∀ y ∈ 𝒮.allCentres, Q ∈ CubeGeometry.activeNear 𝒮 M y →
    supBond (termAtCell Q y f) ≤ linftyBond (cellCutBond y f)
  norm_le : ∀ y ∈ 𝒮.allCentres, Q ∈ CubeGeometry.activeNear 𝒮 M y →
    ltwoBond (termAtCell Q y f) ≤ ltwoBond (cellCutBond y f)
end CellSources
end YangMills.Construction
