import YangMills.Construction.Dirichlet.RegionSequenceOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RegionSequence.NestedRegions
open Torus
variable (𝒮 : NestedRegions)
theorem scale_eq_pow_mul (n : ℕ) : 𝒮.scale n = (𝒮.L : ℝ) ^ n * 𝒮.ξ := by
  simp [scale, scaleSpacing]
theorem Ω_eq_empty_of_lt {n : ℕ} (h : 𝒮.s < n) : 𝒮.Ω n = ∅ := 𝒮.Ω_eq_empty n h
theorem shellOf_eq_empty_of_lt {n : ℕ} (h : 𝒮.s < n) : 𝒮.shellOf n = ∅ := by
  simp [shellOf, shell, 𝒮.Ω_eq_empty_of_lt h]
theorem centresAt_eq_empty_of_lt {n : ℕ} (h : 𝒮.s < n) : 𝒮.centresAt n = ∅ := by
  have hl : shell 𝒮.Ω n = ∅ := 𝒮.shellOf_eq_empty_of_lt h
  simp [centresAt, shellSites, hl]
theorem coarseBonds_eq_empty_of_lt {n : ℕ} (h : 𝒮.s < n) : 𝒮.coarseBonds n = ∅ := by
  have hn : n ≠ 0 := by omega
  simp [coarseBonds, hn, 𝒮.Ω_eq_empty_of_lt h]
def IsPartitionLevel (i : ℕ) : Prop := ∃ k : ℤ, 2 ≤ k ∧ 𝒮.side / 𝒮.scale i = (k : ℝ)
def cubePartitionAt (i : ℕ) : Set (Set 𝒮.Point) := cubePartition 4 𝒮.side (𝒮.scale i)
def IsCubeUnionAt (i : ℕ) (X : Set 𝒮.Point) : Prop := IsCubeUnion (𝒮.scale i) X
def cubeComplementAt (i : ℕ) (X : Set 𝒮.Point) : Set 𝒮.Point := cubeComplement (𝒮.scale i) X
end YangMills.Construction.RegionSequence.NestedRegions
