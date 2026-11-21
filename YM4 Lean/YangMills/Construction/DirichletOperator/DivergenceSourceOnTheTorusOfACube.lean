import YangMills.Construction.DirichletOperator.ScalesOfTheApproximateInverse
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open CubeTorus (torusSetting levelSpacing TensorAnchorSupported)
open CubeOperators (cubeDivOne sourceSize)
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes ApproxInverseScales
namespace ApproxInverseTerms
variable {𝒮 : NestedRegions} {M : ℕ}
structure SourceSplitsAt (Q : LevelCube 𝒮 M) (y' : 𝒮.Point) (J : 𝒮.Tensor 1)
    (k : (torusSetting Q).FineBond → ℝ) : Prop where
  pull_eq : Q.system.pullBonds Q.partitionFn (divOne J) =
    cubeDivOne Q (Q.system.pullTensor Q.partitionFn J) + (levelSpacing Q)⁻¹ • k
  pulled_support : TensorAnchorSupported (cubeHalfSide (Q.system.embed y') (𝒮.levelScale y'))
    (Q.system.pullTensor Q.partitionFn J)
  rest_support : AnchorSupported (cubeHalfSide (Q.system.embed y') (4 * 𝒮.levelScale y')) k
  pulled_sup : supTensor (Q.system.pullTensor Q.partitionFn J) ≤ supTensor J
  pulled_two : ltwoTensor (Q.system.pullTensor Q.partitionFn J) ≤ ltwoTensor J
  pulled_size : ∀ ε : ℝ, 0 ≤ ε → ε < 1 →
    sourceSize ε (𝒮.levelScale y') (Q.system.pullTensor Q.partitionFn J) ≤
      2 * sourceSize ε (𝒮.levelScale y') J
  rest_sup : supBond k ≤ 4 * supTensor J
  rest_two : ltwoBond k ≤ 4 * ltwoTensor J
end ApproxInverseTerms
end YangMills.Construction
