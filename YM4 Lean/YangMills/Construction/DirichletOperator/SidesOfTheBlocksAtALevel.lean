import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes.LevelCubeSides
def Statement : Prop :=
  ∀ (𝒮 : NestedRegions) (K m M R₁ : ℕ), 𝒮.IsLevelUnitChain K m M R₁ →
    ∀ n ≤ topLevel 𝒮,
      (∃ k : ℤ, 𝒮.side / cubeSide 𝒮 M n = 2 * (k : ℝ)) ∧
      2 * cubeSide 𝒮 M n ≤ 𝒮.side ∧
      ∀ c : Fin 4 → ℝ,
        InjOn (torusProj 4 𝒮.side) {p | ∀ μ, |p μ - c μ| < cubeSide 𝒮 M n}
end PartitionCubes.LevelCubeSides
end YangMills.Construction
