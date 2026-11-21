import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PartitionCubes.PartitionSquares
structure SumToOne (S : RegionSequence.NestedRegions) (M : ℕ) : Prop where
  sum_sq : ∀ x : S.Point, ∑ n ∈ Finset.range (topLevel S + 1),
    ∑ᶠ Q ∈ {Q : LevelCube S M | Q.level = n}, Q.partitionFn x ^ 2 = 1
  sum_sq_source : ∀ b ∈ S.bonds,
    ∑ᶠ Q ∈ active S M, Q.partitionFn (b.source : S.Point) ^ 2 = 1
def Statement : Prop :=
  ∀ (K m M R₁ : ℕ) (S : RegionSequence.NestedRegions), S.IsLevelUnitChain K m M R₁ →
    S.L ^ 5 ≤ M → SumToOne S M
end YangMills.Construction.PartitionCubes.PartitionSquares
