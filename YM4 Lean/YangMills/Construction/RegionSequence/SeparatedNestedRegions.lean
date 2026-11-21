import YangMills.Construction.Dirichlet.RegionSequenceOperators
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.RegionSequence
open YangMills.Construction.Torus
namespace NestedRegions
variable (𝒮 : NestedRegions)
def cubeGrid (M : ℕ) (n : ℕ) : Set (Set 𝒮.Point) :=
  cubePartition 4 𝒮.side ((M : ℝ) * 𝒮.scale n)
def exteriorCubes (M : ℕ) (n : ℕ) : Set 𝒮.Point :=
  ⋃₀ {Q ∈ 𝒮.cubeGrid M n | ¬ Q ⊆ 𝒮.Ω n}
structure IsGapSeparated (M R₁ : ℕ) : Prop where
  isPowerGe_block : IsPowerGe 𝒮.L M
  isPowerGe_gap : IsPowerGe 𝒮.L R₁
  side_mem_grid : ∃ k : ℤ, 𝒮.side = (k : ℝ) * (2 * ((M : ℝ) * 𝒮.scale 𝒮.s))
  Ω_eq_sUnion : ∀ n ≤ 𝒮.s, ∃ 𝒞 ⊆ 𝒮.cubeGrid M n, 𝒮.Ω n = ⋃₀ 𝒞
  gap_lt : ∀ n < 𝒮.s, ENNReal.ofReal ((R₁ : ℝ) * (M : ℝ) * 𝒮.scale n) <
    supSetDist (𝒮.exteriorCubes M n) (𝒮.Ω (n + 1))
def chainWeight (Γ : List (TorusSegment 4)) : ℝ :=
  ∑ n ∈ Finset.Icc 1 𝒮.s, (𝒮.scale n)⁻¹ * lengthWithin Γ (𝒮.shellOf n) +
    𝒮.ξ⁻¹ * lengthWithin Γ (𝒮.Ω 1)ᶜ
def weightedDist (y y' : 𝒮.Point) : ℝ :=
  sInf {r | ∃ Γ : List (TorusSegment 4), IsConnected (segmentUnion 𝒮.side Γ) ∧ y ∈ segmentUnion 𝒮.side Γ ∧
    y' ∈ segmentUnion 𝒮.side Γ ∧ r = 𝒮.chainWeight Γ}
end NestedRegions
end YangMills.Construction.RegionSequence
