import YangMills.Construction.DirichletOperator.BoundsOnTheToriOfTheCubes
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.ApproxInverseLaws
open YangMills.Construction.PartitionCubes
structure Laws (𝒮 : RegionSequence.NestedRegions) (M : ℕ) : Prop where
  baseOp_approxInverse : ∀ A ∈ 𝒮.oneForms, baseOp (approxInverse 𝒮 M A) = A - remainderOp 𝒮 M A
  remainderOp_eq : ∀ A ∈ 𝒮.oneForms, ∀ b, remainderOp 𝒮 M A b =
    ∑ᶠ p ∈ active 𝒮 M ×ˢ active 𝒮 M,
      p.1.kernel p.2 (p.2.system.inv (p.2.system.pullBonds p.2.partitionFn A)) b
  bondInner_symm : ∀ A ∈ 𝒮.oneForms, ∀ A' ∈ 𝒮.oneForms,
    bondInner (approxInverse 𝒮 M A) A' = bondInner A (approxInverse 𝒮 M A')
def Claim : Prop :=
  ∀ (K m M R₁ : ℕ) (𝒮 : RegionSequence.NestedRegions), 𝒮.IsLevelUnitChain K m M R₁ →
    max ((𝒮.L : ℝ) ^ 5) ((𝒮.L : ℝ) * (CubeTorus.chosenConstants 𝒮.L).minBlock) ≤ (M : ℝ) →
      Laws 𝒮 M
end YangMills.Construction.ApproxInverseLaws
end
