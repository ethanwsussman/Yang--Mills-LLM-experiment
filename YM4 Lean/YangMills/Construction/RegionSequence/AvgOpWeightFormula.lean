import YangMills.Construction.Dirichlet.RegionSequenceOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence
open NestedRegions
def AvgOpByWeights : Prop :=
  ∀ 𝒯 : NestedRegions,
    (∀ (n : ℕ) (c : 𝒯.BondAt n) (A : 𝒯.FineBond → ℝ),
      bondAvg n A c = ∑ᶠ b, avgWeight n c b * A b) ∧
    ∀ A : 𝒯.FineBond → ℝ, avgOp A ∈ 𝒯.oneForms ∧
      (∀ A' ∈ 𝒯.oneForms, bondInner (avgOp A) A' = avgForm A A') ∧
      ∀ b ∈ 𝒯.bonds, avgOp A b =
        (𝒯.ξ ^ 4)⁻¹ * ∑ j ∈ Finset.range (𝒯.s + 1), ∑ᶠ c ∈ 𝒯.coarseBonds j,
          gaugeParam * 𝒯.scale j ^ (4 - 2) * avgWeight j c b * bondAvg j A c
end YangMills.Construction.RegionSequence
