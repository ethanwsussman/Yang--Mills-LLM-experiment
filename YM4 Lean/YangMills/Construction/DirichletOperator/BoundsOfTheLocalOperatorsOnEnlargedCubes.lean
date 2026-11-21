import YangMills.Construction.DirichletOperator.ScalesOfTheApproximateInverse
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Dirichlet RegionSequence RegionSequence.NestedRegions PartitionCubes
open CubeTorus (torusSetting levelSpacing tensorModulusAt TensorAnchorSupported)
open CubeOperators (RegularityConstants cubeDivOne cubeDivTwo IsCubeScale cutoffSize
  sourceSize chosenConstants)
namespace EnlargedCubeBounds
variable {𝒮 : NestedRegions} {M : ℕ}
structure EnlargedKernelBounds (c : RegularityConstants) (C : ℝ) (Q : LevelCube 𝒮 M)
    (o o' : (torusSetting Q).Point) (r₁ r₂ : ℝ) : Prop where
  value : ∀ J ∈ Q.system.forms, AnchorSupported (cubeHalfSide o' (4 * r₂)) J →
    ∀ x, AnchoredIn (cubeHalfSide o (4 * r₁)) x →
      |Q.system.inv J x| ≤ C * (c.B * levelSpacing Q ^ 2 * c.expDecay Q o o' * supBond J)
  difference : ∀ J ∈ Q.system.forms, AnchorSupported (cubeHalfSide o' (4 * r₂)) J →
    ∀ x, AnchoredIn (cubeHalfSide o (4 * r₁)) x →
      tensorModulusAt (nablaOne (Q.system.inv J)) x ≤
        C * (c.B * levelSpacing Q * c.expDecay Q o o' * supBond J)
  source : ∀ J : (torusSetting Q).Tensor 1,
    TensorAnchorSupported (cubeHalfSide o' (4 * r₂)) J →
    ∀ x, AnchoredIn (cubeHalfSide o (4 * r₁)) x →
      |Q.system.inv (cubeDivOne Q J) x| ≤
        C * (c.B * levelSpacing Q * c.expDecay Q o o' * supTensor J)
  laplacian : ∀ J ∈ Q.system.forms, AnchorSupported (cubeHalfSide o' (4 * r₂)) J →
    ∀ x, AnchoredIn (cubeHalfSide o (4 * r₁)) x →
      |bondLap (Q.system.inv J) x| ≤ C * (c.B * c.expDecay Q o o' * supBond J)
  value_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ η : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cubeHalfSide o r₁) η → ∀ J ∈ Q.system.forms,
    AnchorSupported (cubeHalfSide o' (4 * r₂)) J →
      (levelSpacing Q)⁻¹ * holderBond α r₁ (smulSiteBond η (Q.system.inv J)) ≤
        C * (c.Bα α * levelSpacing Q * cutoffSize α r₁ η * c.expDecay Q o o' * supBond J)
  difference_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ η : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cubeHalfSide o r₁) η → ∀ J ∈ Q.system.forms,
    AnchorSupported (cubeHalfSide o' (4 * r₂)) J →
      holderTensor α r₁ (smulSiteTensor η (nablaOne (Q.system.inv J))) ≤
        C * (c.Bα α * levelSpacing Q * cutoffSize α r₁ η * c.expDecay Q o o' * supBond J)
  source_holder : ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ η : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cubeHalfSide o r₁) η → ∀ J : (torusSetting Q).Tensor 1,
    TensorAnchorSupported (cubeHalfSide o' (4 * r₂)) J →
      holderBond α r₁ (smulSiteBond η (Q.system.inv (cubeDivOne Q J))) ≤
        C * (c.Bα α * levelSpacing Q * cutoffSize α r₁ η * c.expDecay Q o o' * supTensor J)
  source_difference : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ J : (torusSetting Q).Tensor 1,
    TensorAnchorSupported (cubeHalfSide o' r₂) J →
    ∀ x, AnchoredIn (cubeHalfSide o (4 * r₁)) x →
      tensorModulusAt (nablaOne (Q.system.inv (cubeDivOne Q J))) x ≤
        C * (c.Bε ε * c.expDecay Q o o' * sourceSize ε r₂ J)
  value_two : ∀ η : (torusSetting Q).FineSite → ℝ, VanishesOff (cubeHalfSide o r₁) η →
    ∀ J ∈ Q.system.forms, AnchorSupported (cubeHalfSide o' (4 * r₂)) J →
      ltwoBond (smulSiteBond η (Q.system.inv J)) ≤
        C * (c.B * levelSpacing Q ^ 2 * supSite η * c.expDecay Q o o' * ltwoBond J)
  difference_two : ∀ η : (torusSetting Q).FineSite → ℝ, VanishesOff (cubeHalfSide o r₁) η →
    ∀ J ∈ Q.system.forms, AnchorSupported (cubeHalfSide o' (4 * r₂)) J →
      ltwoTensor (smulSiteTensor η (nablaOne (Q.system.inv J))) ≤
        C * (c.B * levelSpacing Q * supSite η * c.expDecay Q o o' * ltwoBond J)
  source_two : ∀ η : (torusSetting Q).FineSite → ℝ, VanishesOff (cubeHalfSide o r₁) η →
    ∀ J : (torusSetting Q).Tensor 1, TensorAnchorSupported (cubeHalfSide o' (4 * r₂)) J →
      ltwoBond (smulSiteBond η (Q.system.inv (cubeDivOne Q J))) ≤
        C * (c.B * levelSpacing Q * supSite η * c.expDecay Q o o' * ltwoTensor J)
  source_difference_two : ∀ η : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cubeHalfSide o r₁) η → ∀ J : (torusSetting Q).Tensor 1,
    TensorAnchorSupported (cubeHalfSide o' (4 * r₂)) J →
      ltwoTensor (smulSiteTensor η (nablaOne (Q.system.inv (cubeDivOne Q J)))) ≤
        C * (c.B * supSite η * c.expDecay Q o o' * ltwoTensor J)
  second_difference_two : ∀ η : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cubeHalfSide o r₁) η → ∀ J ∈ Q.system.forms,
    AnchorSupported (cubeHalfSide o' (4 * r₂)) J →
      ltwoTensor (smulSiteTensor η (nablaTwo (nablaOne (Q.system.inv J)))) ≤
        C * (c.B * supSite η * c.expDecay Q o o' * ltwoBond J)
  second_source_two : ∀ η : (torusSetting Q).FineSite → ℝ,
    VanishesOff (cubeHalfSide o r₁) η → ∀ J : (torusSetting Q).Tensor 2,
    TensorAnchorSupported (cubeHalfSide o' (4 * r₂)) J →
      ltwoBond (smulSiteBond η (Q.system.inv (cubeDivTwo Q J))) ≤
        C * (c.B * supSite η * c.expDecay Q o o' * ltwoTensor J)
end EnlargedCubeBounds
end YangMills.Construction
