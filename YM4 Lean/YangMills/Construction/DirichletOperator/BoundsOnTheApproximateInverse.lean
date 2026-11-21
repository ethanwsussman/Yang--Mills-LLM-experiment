import YangMills.Construction.DirichletOperator.ScalesOfTheApproximateInverse
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes
open CubeTorus (TensorAnchorSupported)
open CubeOperators (cutoffSize sourceSize)
open ApproxInverseScales
noncomputable section
namespace ApproxInverseBounds
structure Constants where
  B : ℝ
  Bα : ℝ → ℝ
  Bε : ℝ → ℝ
  Bαε : ℝ → ℝ → ℝ
instance : Inhabited Constants := ⟨⟨0, fun _ => 0, fun _ => 0, fun _ _ => 0⟩⟩
variable {𝒮 : NestedRegions}
structure BothBounds (M : ℕ) (p : ((𝒮.FineBond → ℝ) → 𝒮.FineBond → ℝ) → ℝ) (r : ℝ) : Prop where
  approx : p (approxInverse 𝒮 M) ≤ r
  cube_sum : ∑ᶠ Q ∈ active 𝒮 M, p Q.invTerm ≤ r
namespace Constants
variable (c : Constants)
structure Estimates (M : ℕ) (y y' : 𝒮.Point) : Prop where
  value : ∀ f ∈ 𝒮.oneForms, BothBounds M
    (fun T => (𝒮.levelScale y ^ 2)⁻¹ * supBond (restrictBonds (outerCube y) (T f)))
    (c.B * weightedSourceSum linftyBond y f)
  difference : ∀ f ∈ 𝒮.oneForms, BothBounds M
    (fun T => (𝒮.levelScale y)⁻¹ * supTensor (restrictTensor (outerCube y) (nablaOne (T f))))
    (c.B * weightedSourceSum linftyBond y f)
  laplacian : ∀ f ∈ 𝒮.oneForms, BothBounds M
    (fun T => supBond (restrictBonds (outerCube y) (bondLap (T f))))
    (c.B * weightedSourceSum linftyBond y f)
  difference_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ : 𝒮.FineSite → ℝ,
    VanishesOff (cubeHalfSide y (𝒮.levelScale y)) ζ → ∀ f ∈ 𝒮.oneForms, BothBounds M
      (fun T => (𝒮.levelScale y)⁻¹ *
        holderTensor α (𝒮.levelScale y) (smulSiteTensor ζ (nablaOne (T f))))
      (c.Bα α * cutoffSize α (𝒮.levelScale y) ζ * weightedSourceSum linftyBond y f)
  value_two : ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (cubeHalfSide y (𝒮.levelScale y)) ζ →
    ∀ f ∈ 𝒮.oneForms, BothBounds M
      (fun T => (𝒮.levelScale y ^ 2)⁻¹ * ltwoBond (smulSiteBond ζ (T f)))
      (c.B * supSite ζ * weightedSourceSum ltwoBond y f)
  difference_two : ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (cubeHalfSide y (𝒮.levelScale y)) ζ →
    ∀ f ∈ 𝒮.oneForms, BothBounds M
      (fun T => (𝒮.levelScale y)⁻¹ * ltwoTensor (smulSiteTensor ζ (nablaOne (T f))))
      (c.B * supSite ζ * weightedSourceSum ltwoBond y f)
  second_difference_two : ∀ ζ : 𝒮.FineSite → ℝ,
    VanishesOff (cubeHalfSide y (𝒮.levelScale y)) ζ → ∀ f ∈ 𝒮.oneForms, BothBounds M
      (fun T => ltwoTensor (smulSiteTensor ζ (nablaTwo (nablaOne (T f)))))
      (c.B * supSite ζ * weightedSourceSum ltwoBond y f)
  source : ∀ J : 𝒮.Tensor 1, TensorAnchorSupported (cubeHalfSide y' (𝒮.levelScale y')) J →
    BothBounds M
      (fun T => (𝒮.levelScale y)⁻¹ * supBond (restrictBonds (outerCube y) (T (divOne J))))
      (c.B * expWeight y y' * supTensor J)
  source_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ ζ : 𝒮.FineSite → ℝ,
    VanishesOff (cubeHalfSide y (𝒮.levelScale y)) ζ → ∀ J : 𝒮.Tensor 1,
    TensorAnchorSupported (cubeHalfSide y' (𝒮.levelScale y')) J → BothBounds M
      (fun T => (𝒮.levelScale y)⁻¹ *
        holderBond α (𝒮.levelScale y) (smulSiteBond ζ (T (divOne J))))
      (c.Bα α * cutoffSize α (𝒮.levelScale y) ζ * expWeight y y' * supTensor J)
  source_difference : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ J : 𝒮.Tensor 1,
    TensorAnchorSupported (cubeHalfSide y' (𝒮.levelScale y')) J → BothBounds M
      (fun T => supTensor (restrictTensor (outerCube y) (nablaOne (T (divOne J)))))
      (c.Bε ε * expWeight y y' * sourceSize ε (𝒮.levelScale y') J)
  source_difference_holder : ∀ α ε : ℝ, 0 ≤ α → α < 1 → 0 < ε → α + ε < 1 →
    ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (cubeHalfSide y (𝒮.levelScale y)) ζ →
    ∀ J : 𝒮.Tensor 1, TensorAnchorSupported (cubeHalfSide y' (𝒮.levelScale y')) J →
    BothBounds M
      (fun T => holderTensor α (𝒮.levelScale y)
        (smulSiteTensor ζ (nablaOne (T (divOne J)))))
      (c.Bαε α ε * cutoffSize α (𝒮.levelScale y) ζ * expWeight y y' *
        sourceSize (α + ε) (𝒮.levelScale y') J)
  source_two : ∀ ζ : 𝒮.FineSite → ℝ, VanishesOff (cubeHalfSide y (𝒮.levelScale y)) ζ →
    ∀ J : 𝒮.Tensor 1, TensorAnchorSupported (cubeHalfSide y' (𝒮.levelScale y')) J →
    BothBounds M
      (fun T => (𝒮.levelScale y)⁻¹ * ltwoBond (smulSiteBond ζ (T (divOne J))))
      (c.B * supSite ζ * expWeight y y' * ltwoTensor J)
  source_difference_two : ∀ ζ : 𝒮.FineSite → ℝ,
    VanishesOff (cubeHalfSide y (𝒮.levelScale y)) ζ → ∀ J : 𝒮.Tensor 1,
    TensorAnchorSupported (cubeHalfSide y' (𝒮.levelScale y')) J → BothBounds M
      (fun T => ltwoTensor (smulSiteTensor ζ (nablaOne (T (divOne J)))))
      (c.B * supSite ζ * expWeight y y' * ltwoTensor J)
  second_source_two : ∀ ζ : 𝒮.FineSite → ℝ,
    VanishesOff (cubeHalfSide y (𝒮.levelScale y)) ζ → ∀ J : 𝒮.Tensor 2,
    TensorAnchorSupported (cubeHalfSide y' (𝒮.levelScale y')) J → BothBounds M
      (fun T => ltwoBond (smulSiteBond ζ (T (divTwo J))))
      (c.B * supSite ζ * expWeight y y' * ltwoTensor J)
def Valid (L : ℕ) : Prop :=
  ∀ (K m M R₁ : ℕ) (𝒮 : NestedRegions), 𝒮.L = L → 𝒮.IsLevelUnitChain K m M R₁ →
    blockLowerBound L ≤ (M : ℝ) → ∀ y ∈ 𝒮.allCentres, ∀ y' ∈ 𝒮.allCentres, c.Estimates M y y'
end Constants
def chosenConstants (L : ℕ) : Constants := Classical.epsilon fun c : Constants => c.Valid L
end ApproxInverseBounds
end
end YangMills.Construction
