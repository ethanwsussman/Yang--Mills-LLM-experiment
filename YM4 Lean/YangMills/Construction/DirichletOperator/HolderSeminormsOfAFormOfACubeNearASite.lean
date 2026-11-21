import YangMills.Construction.DirichletOperator.ScalesOfTheApproximateInverse
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.CubeFormHolder
open Dirichlet RegionSequence RegionSequence.NestedRegions PartitionCubes
variable {𝒮 : NestedRegions} {M : ℕ}
structure IsLocalRepresentation (Q : LevelCube 𝒮 M) (y : 𝒮.Point) (α : ℝ) (ζ f : 𝒮.FineSite → ℝ)
    (g : Q.system.setting.FineSite → ℝ) : Prop where
  vanishes_off : VanishesOff (cubeHalfSide (Q.system.embed y) (𝒮.levelScale y)) g
  agrees : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ cubeHalfSide y (𝒮.levelScale y) →
    g (Q.system.mapSite x) = f x
  size_le : CubeOperators.cutoffSize α (𝒮.levelScale y) g ≤
    2 * CubeOperators.cutoffSize α (𝒮.levelScale y) ζ
end YangMills.Construction.CubeFormHolder
