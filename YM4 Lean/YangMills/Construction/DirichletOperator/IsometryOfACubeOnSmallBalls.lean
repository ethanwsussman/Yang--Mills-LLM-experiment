import YangMills.Construction.DirichletOperator.CellsOfACube
import YangMills.Construction.DirichletOperator.FactsOfALocalOperatorOfACube
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
structure LevelCube.IsometricOnBalls (Q : LevelCube 𝒮 M) : Prop where
  ball_bijOn : ∀ s ∈ Q.thicken (5 / 6),
    BijOn Q.system.embed {x | Torus.supNorm (x - s) ≤ 4 * 𝒮.scale (Q.level + 1)}
      {x | Torus.supNorm (x - Q.system.embed s) ≤ 4 * 𝒮.scale (Q.level + 1)}
  lOneNorm_eq : ∀ s ∈ Q.thicken (5 / 6), ∀ x x' : 𝒮.Point,
    Torus.supNorm (x - s) ≤ 4 * 𝒮.scale (Q.level + 1) →
    Torus.supNorm (x' - s) ≤ 4 * 𝒮.scale (Q.level + 1) →
      Torus.lOneNorm (Q.system.embed x - Q.system.embed x') = Torus.lOneNorm (x - x')
  supNorm_eq : ∀ s ∈ Q.thicken (5 / 6), ∀ x x' : 𝒮.Point,
    Torus.supNorm (x - s) ≤ 4 * 𝒮.scale (Q.level + 1) →
    Torus.supNorm (x' - s) ≤ 4 * 𝒮.scale (Q.level + 1) →
      Torus.supNorm (Q.system.embed x - Q.system.embed x') = Torus.supNorm (x - x')
  thickened_image : ∀ y ∈ 𝒮.allCentres, (𝒮.cellOf y ∩ Q.thicken (5 / 6)).Nonempty →
    Q.thickened (Q.system.embed '' 𝒮.cellOf y) = Q.system.embed '' Q.nearSet (𝒮.cellOf y)
end YangMills.Construction.PartitionCubes
