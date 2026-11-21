import YangMills.Construction.PartitionCubes.LocalOperators
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes
structure IsCubeSetting (𝒯 : NestedRegions) (n : ℕ) : Prop where
  top_level : 𝒯.s = n + 1
  bonds_univ : 𝒯.bonds = univ
  full_below : ∀ j ≤ n, 𝒯.Ω j = univ
def IsLipschitzAtScale {𝒯 : NestedRegions} (n : ℕ) (κ : ℝ) (φ : 𝒯.Point → ℝ) : Prop :=
  ∀ x y : 𝒯.Point, supNorm (x - y) ≤ 2 * 𝒯.scale (n + 1) →
    |φ x - φ y| ≤ κ * lOneNorm (x - y)
end PartitionCubes
end YangMills.Construction
