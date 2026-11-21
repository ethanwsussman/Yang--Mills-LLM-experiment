import YangMills.Construction.DirichletOperator.ScalesOfTheApproximateInverse
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.CubeTermNorms
open RegionSequence RegionSequence.NestedRegions PartitionCubes ApproxInverseScales
variable {𝒮 : NestedRegions} {M : ℕ}
structure TermBounds (C : ℝ) (Q : LevelCube 𝒮 M) (y : 𝒮.Point) (ζ : 𝒮.FineSite → ℝ)
    (f : 𝒮.FineBond → ℝ) : Prop where
  value_two : (𝒮.levelScale y ^ 2)⁻¹ * ltwoBond (smulSiteBond ζ (Q.invTerm f)) ≤
    C * supSite ζ * weightedSourceSum ltwoBond y f
  difference_two : (𝒮.levelScale y)⁻¹ *
      ltwoTensor (smulSiteTensor ζ (nablaOne (Q.invTerm f))) ≤
    C * supSite ζ * weightedSourceSum ltwoBond y f
  second_difference_two :
    ltwoTensor (smulSiteTensor ζ (nablaTwo (nablaOne (Q.invTerm f)))) ≤
      C * supSite ζ * weightedSourceSum ltwoBond y f
end YangMills.Construction.CubeTermNorms
end
