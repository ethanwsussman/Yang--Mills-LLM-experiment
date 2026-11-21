import YangMills.Construction.DirichletOperator.BoundsOnTheToriOfTheCubes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
namespace PartitionCubes
def DefectEqFinsumKernels : Prop :=
  ∀ (K m M R₁ : ℕ) (𝒮 : NestedRegions), 𝒮.IsLevelUnitChain K m M R₁ →
    max ((𝒮.L : ℝ) ^ 5) ((𝒮.L : ℝ) * (CubeTorus.chosenConstants 𝒮.L).minBlock) ≤ (M : ℝ) →
    ∀ Q ∈ active 𝒮 M, ∀ v ∈ Q.system.forms, ∀ b,
      Q.defectOp v b = ∑ᶠ Q' ∈ active 𝒮 M, Q'.kernel Q v b
end PartitionCubes
end YangMills.Construction
