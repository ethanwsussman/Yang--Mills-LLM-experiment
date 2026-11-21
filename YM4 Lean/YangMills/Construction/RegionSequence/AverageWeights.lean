import YangMills.Construction.Dirichlet.RegionSequenceOperators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RegionSequence
open NestedRegions
structure AvgWeightProps (𝒮 : NestedRegions) : Prop where
  avgWeight_nonneg : ∀ n, ∀ c ∈ 𝒮.coarseBonds n, ∀ b, 0 ≤ avgWeight n c b
  avgWeight_sum : ∀ n, ∀ c ∈ 𝒮.coarseBonds n, ∑ᶠ b, avgWeight n c b = 1
  avgWeight_le : ∀ n, ∀ c ∈ 𝒮.coarseBonds n, ∀ b, avgWeight n c b ≤ ((𝒮.L : ℝ) ^ (n * 4))⁻¹
  avgWeight_support : ∀ n, ∀ c ∈ 𝒮.coarseBonds n, ∀ b, avgWeight n c b ≠ 0 →
    b.dir = c.dir ∧
      (b.source ∈ 𝒮.fineBlock n (c.source : 𝒮.Point) ∨ b.source ∈ 𝒮.fineBlock n (c.target : 𝒮.Point))
end YangMills.Construction.RegionSequence
