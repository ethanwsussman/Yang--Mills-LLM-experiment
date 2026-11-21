import YangMills.Construction.Dirichlet.RegionSequenceOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence
open Dirichlet Torus NestedRegions
variable (𝒮 : NestedRegions)
structure BlockAverageAdjointFacts : Prop where
  blockAvgAdj_apply : ∀ ω : 𝒮.Coarse, blockAvgAdj ω ∈ 𝒮.siteFns ∧
    ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ 𝒮.Ω 0 → ∃ h : 𝒮.centreOfSite x ∈ 𝒮.allCentres,
      blockAvgAdj ω x = ω ⟨𝒮.centreOfSite x, h⟩
  blockAvg_blockAvgAdj : ∀ ω : 𝒮.Coarse, blockAvg (blockAvgAdj ω) = ω
  blockAvgAdj_injective : Function.Injective (blockAvgAdj (𝒮 := 𝒮))
  weighted_apply : ∀ f ∈ 𝒮.siteFns, ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ 𝒮.Ω 0 →
    ∃ h : 𝒮.centreOfSite x ∈ 𝒮.allCentres,
      blockAvgAdj (weightMul (blockAvg f)) x =
        blockWeights 𝒮.L (𝒮.level (𝒮.centreOfSite x)) *
          (𝒮.scale (𝒮.level (𝒮.centreOfSite x)) ^ 2)⁻¹ * blockAvg f ⟨𝒮.centreOfSite x, h⟩
  abs_blockAvg_le : ∀ f ∈ 𝒮.siteFns, ∀ y : 𝒮.allCentres,
    |blockAvg f y| ≤ supNormOn (𝒮.cellOf y) f
end YangMills.Construction.RegionSequence
