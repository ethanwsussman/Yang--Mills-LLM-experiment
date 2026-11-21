import YangMills.Construction.DirichletOperator.ScalesOfTheApproximateInverse
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes ApproxInverseScales
namespace ApproxInverseTerms
variable {𝒮 : NestedRegions}
structure TermsVanishAt (y : 𝒮.Point) (A : 𝒮.FineBond → ℝ) : Prop where
  value : restrictBonds (outerCube y) A = 0
  grad : restrictTensor (outerCube y) (nablaOne A) = 0
  lap : restrictBonds (outerCube y) (bondLap A) = 0
  smul_value : ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (cubeHalfSide y (𝒮.levelScale y)) ζ →
    smulSiteBond ζ A = 0
  smul_grad : ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (cubeHalfSide y (𝒮.levelScale y)) ζ →
    smulSiteTensor ζ (nablaOne A) = 0
  smul_grad_grad : ∀ ζ : 𝒮.FineSite → ℝ,
    VanishesOff (cubeHalfSide y (𝒮.levelScale y)) ζ →
    smulSiteTensor ζ (nablaTwo (nablaOne A)) = 0
end ApproxInverseTerms
end YangMills.Construction
