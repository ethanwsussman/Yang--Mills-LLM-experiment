import YangMills.Construction.DirichletOperator.BoundsOnTheToriOfTheCubes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes
open YangMills.Construction.CubeTorus (TensorAnchorSupported tensorModulusAt)
namespace GreenRegularity
structure Constants where
  δ : ℝ
  B : ℝ
  Bα : ℝ → ℝ
  Bε : ℝ → ℝ
  Bαε : ℝ → ℝ → ℝ
structure Data (𝒯 : NestedRegions) where
  space : Submodule ℝ (𝒯.FineBond → ℝ)
  op : (𝒯.FineBond → ℝ) → 𝒯.FineBond → ℝ
  divOne : 𝒯.Tensor 1 → 𝒯.FineBond → ℝ
  divTwo : 𝒯.Tensor 2 → 𝒯.FineBond → ℝ
  scale : ℝ
  scaleNext : ℝ
variable {𝒯 : NestedRegions}
def Data.inv (P : Data 𝒯) (v : 𝒯.FineBond → ℝ) : 𝒯.FineBond → ℝ :=
  inverseValue (P.space : Set (𝒯.FineBond → ℝ)) P.op v
def cutoffNormSum (α t : ℝ) (φ : 𝒯.FineSite → ℝ) : ℝ := holderSite α t φ + supSite φ
def sourceNormSum {r : ℕ} (ε t : ℝ) (F : 𝒯.Tensor r) : ℝ :=
  holderTensor ε t F + supTensor F
namespace Constants
variable (c : Constants) (P : Data 𝒯)
def expWeight (p q : 𝒯.Point) : ℝ := Real.exp (-c.δ * (P.scale⁻¹ * lOneNorm (p - q)))
structure Estimates (p q : 𝒯.Point) (t₁ t₂ : ℝ) : Prop where
  value : ∀ F ∈ P.space, AnchorSupported (cubeHalfSide q t₂) F →
    ∀ x, AnchoredIn (cubeHalfSide p t₁) x →
      |P.inv F x| ≤ c.B * P.scale ^ 2 * c.expWeight P p q * supBond F
  difference : ∀ F ∈ P.space, AnchorSupported (cubeHalfSide q t₂) F →
    ∀ x, AnchoredIn (cubeHalfSide p t₁) x →
      tensorModulusAt (nablaOne (P.inv F)) x ≤ c.B * P.scale * c.expWeight P p q * supBond F
  source : ∀ F : 𝒯.Tensor 1, TensorAnchorSupported (cubeHalfSide q t₂) F →
    ∀ x, AnchoredIn (cubeHalfSide p t₁) x →
      |P.inv (P.divOne F) x| ≤ c.B * P.scale * c.expWeight P p q * supTensor F
  laplacian : ∀ F ∈ P.space, AnchorSupported (cubeHalfSide q t₂) F →
    ∀ x, AnchoredIn (cubeHalfSide p t₁) x →
      |bondLap (P.inv F) x| ≤ c.B * c.expWeight P p q * supBond F
  value_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ φ : 𝒯.FineSite → ℝ,
    VanishesOff (cubeHalfSide p t₁) φ → ∀ F ∈ P.space,
    AnchorSupported (cubeHalfSide q t₂) F →
      (P.scale)⁻¹ * holderBond α t₁ (smulSiteBond φ (P.inv F)) ≤
        c.Bα α * P.scale * cutoffNormSum α t₁ φ * c.expWeight P p q * supBond F
  difference_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ φ : 𝒯.FineSite → ℝ,
    VanishesOff (cubeHalfSide p t₁) φ → ∀ F ∈ P.space,
    AnchorSupported (cubeHalfSide q t₂) F →
      holderTensor α t₁ (smulSiteTensor φ (nablaOne (P.inv F))) ≤
        c.Bα α * P.scale * cutoffNormSum α t₁ φ * c.expWeight P p q * supBond F
  source_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ φ : 𝒯.FineSite → ℝ,
    VanishesOff (cubeHalfSide p t₁) φ → ∀ F : 𝒯.Tensor 1,
    TensorAnchorSupported (cubeHalfSide q t₂) F →
      holderBond α t₁ (smulSiteBond φ (P.inv (P.divOne F))) ≤
        c.Bα α * P.scale * cutoffNormSum α t₁ φ * c.expWeight P p q * supTensor F
  source_difference : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ F : 𝒯.Tensor 1,
    TensorAnchorSupported (cubeHalfSide q t₂) F → ∀ x, AnchoredIn (cubeHalfSide p t₁) x →
      tensorModulusAt (nablaOne (P.inv (P.divOne F))) x ≤
        c.Bε ε * c.expWeight P p q * sourceNormSum ε t₂ F
  source_difference_holder : ∀ α ε : ℝ, 0 ≤ α → α < 1 → 0 < ε → α + ε < 1 →
    ∀ φ : 𝒯.FineSite → ℝ, VanishesOff (cubeHalfSide p t₁) φ →
    ∀ F : 𝒯.Tensor 1, TensorAnchorSupported (cubeHalfSide q t₂) F →
      holderTensor α t₁
          (smulSiteTensor φ (nablaOne (P.inv (P.divOne F)))) ≤
        c.Bαε α ε * cutoffNormSum α t₁ φ * c.expWeight P p q * sourceNormSum (α + ε) t₂ F
  value_two : ∀ φ : 𝒯.FineSite → ℝ, VanishesOff (cubeHalfSide p t₁) φ →
    ∀ F ∈ P.space, AnchorSupported (cubeHalfSide q t₂) F →
      ltwoBond (smulSiteBond φ (P.inv F)) ≤
        c.B * P.scale ^ 2 * supSite φ * c.expWeight P p q * ltwoBond F
  difference_two : ∀ φ : 𝒯.FineSite → ℝ, VanishesOff (cubeHalfSide p t₁) φ →
    ∀ F ∈ P.space, AnchorSupported (cubeHalfSide q t₂) F →
      ltwoTensor (smulSiteTensor φ (nablaOne (P.inv F))) ≤
        c.B * P.scale * supSite φ * c.expWeight P p q * ltwoBond F
  source_two : ∀ φ : 𝒯.FineSite → ℝ, VanishesOff (cubeHalfSide p t₁) φ →
    ∀ F : 𝒯.Tensor 1, TensorAnchorSupported (cubeHalfSide q t₂) F →
      ltwoBond (smulSiteBond φ (P.inv (P.divOne F))) ≤
        c.B * P.scale * supSite φ * c.expWeight P p q * ltwoTensor F
  source_difference_two : ∀ φ : 𝒯.FineSite → ℝ,
    VanishesOff (cubeHalfSide p t₁) φ → ∀ F : 𝒯.Tensor 1,
    TensorAnchorSupported (cubeHalfSide q t₂) F →
      ltwoTensor (smulSiteTensor φ (nablaOne (P.inv (P.divOne F)))) ≤
        c.B * supSite φ * c.expWeight P p q * ltwoTensor F
  second_difference_two : ∀ φ : 𝒯.FineSite → ℝ,
    VanishesOff (cubeHalfSide p t₁) φ → ∀ F ∈ P.space,
    AnchorSupported (cubeHalfSide q t₂) F →
      ltwoTensor (smulSiteTensor φ (nablaTwo (nablaOne (P.inv F)))) ≤
        c.B * supSite φ * c.expWeight P p q * ltwoBond F
  second_source_two : ∀ φ : 𝒯.FineSite → ℝ,
    VanishesOff (cubeHalfSide p t₁) φ → ∀ F : 𝒯.Tensor 2,
    TensorAnchorSupported (cubeHalfSide q t₂) F →
      ltwoBond (smulSiteBond φ (P.inv (P.divTwo F))) ≤
        c.B * supSite φ * c.expWeight P p q * ltwoTensor F
structure Valid : Prop where
  invertible : BijOn P.op (P.space : Set (𝒯.FineBond → ℝ)) P.space
  symmetric : ∀ u ∈ P.space, ∀ v ∈ P.space, bondInner (P.inv u) v = bondInner u (P.inv v)
  bounds : ∀ t₁ t₂ : ℝ, (t₁ = P.scale ∨ t₁ = P.scaleNext) →
    (t₂ = P.scale ∨ t₂ = P.scaleNext) → ∀ p q : 𝒯.Point, c.Estimates P p q t₁ t₂
end Constants
end GreenRegularity
end YangMills.Construction
