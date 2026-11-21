import YangMills.Construction.DirichletOperator.ScalesOfTheApproximateInverse
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.CubeTermDivergence
open Dirichlet RegionSequence RegionSequence.NestedRegions PartitionCubes ApproxInverseScales
variable {𝒮 : NestedRegions} {M : ℕ}
structure L2Bounds (C : ℝ) (Q : LevelCube 𝒮 M) (y y' : 𝒮.Point) (ζ : 𝒮.FineSite → ℝ) : Prop where
  div_two : ∀ J : 𝒮.Tensor 1,
    CubeTorus.TensorAnchorSupported (cubeHalfSide y' (𝒮.levelScale y')) J →
    (𝒮.levelScale y)⁻¹ * ltwoBond (smulSiteBond ζ (Q.invTerm (divOne J))) ≤
      C * supSite ζ * expWeight y y' * ltwoTensor J
  grad_div_two : ∀ J : 𝒮.Tensor 1,
    CubeTorus.TensorAnchorSupported (cubeHalfSide y' (𝒮.levelScale y')) J →
    ltwoTensor (smulSiteTensor ζ (nablaOne (Q.invTerm (divOne J)))) ≤
      C * supSite ζ * expWeight y y' * ltwoTensor J
  divdiv_two : ∀ J : 𝒮.Tensor 2,
    CubeTorus.TensorAnchorSupported (cubeHalfSide y' (𝒮.levelScale y')) J →
    ltwoBond (smulSiteBond ζ (Q.invTerm (divTwo J))) ≤
      C * supSite ζ * expWeight y y' * ltwoTensor J
end YangMills.Construction.CubeTermDivergence
