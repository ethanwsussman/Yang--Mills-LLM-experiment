import YangMills.Construction.Dirichlet.LatticeCalculus
import YangMills.Construction.Dirichlet.Parameters
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
noncomputable section
namespace YangMills.Construction.WeightedLength
variable {d L : ℕ} {aMinus aPlus S : ℝ}
def IsSegmentChain (S : ℝ) : PeriodicTorus d S → List (TorusSegment d) → PeriodicTorus d S → Prop
  | _, [], _ => False
  | p, [σ], q => σ.pointAt S 0 = p ∧ σ.pointAt S 1 = q
  | p, σ :: σ' :: Γ, q => σ.pointAt S 0 = p ∧ IsSegmentChain S (σ.pointAt S 1) (σ' :: Γ) q
structure Bounds (𝒮 : BlockSetting d L aMinus aPlus S) : Prop where
  dist_triangle : ∀ p q q' : PeriodicTorus d S, 𝒮.blockDist p q' ≤ 𝒮.blockDist p q + 𝒮.blockDist q q'
  le_chainLength : ∀ m : ℕ, m ≤ 𝒮.t → ∀ (γ : List (TorusSegment d)) (p q : PeriodicTorus d S),
    IsSegmentChain S p γ q → (segmentUnion S γ ∩ 𝒮.Ω (m + 1)).Finite →
      (𝒮.scaleAt m)⁻¹ * lOneNorm (p - q) ≤ chainWeightedLength L 𝒮.ξ 𝒮.t 𝒮.Ω γ
  neighbor_dist_le : ∀ x x' : LatticeSite d S 𝒮.ξ, IsNeighbor x x' →
    𝒮.blockDist (x : PeriodicTorus d S) (x' : PeriodicTorus d S) ≤
        1 / 2 * 𝒮.ξ * ((𝒮.localScale x)⁻¹ + (𝒮.localScale x')⁻¹) ∧
      1 / 2 * 𝒮.ξ * ((𝒮.localScale x)⁻¹ + (𝒮.localScale x')⁻¹) ≤
        𝒮.ξ / min (𝒮.localScale x) (𝒮.localScale x') ∧
      𝒮.ξ / min (𝒮.localScale x) (𝒮.localScale x') ≤ 1
def HoldsForAll : Prop :=
  ∀ (d L : ℕ) (aMinus aPlus : ℝ), Parameters d L aMinus aPlus →
    ∀ (S : ℝ) (𝒮 : BlockSetting d L aMinus aPlus S), Bounds 𝒮
end YangMills.Construction.WeightedLength
