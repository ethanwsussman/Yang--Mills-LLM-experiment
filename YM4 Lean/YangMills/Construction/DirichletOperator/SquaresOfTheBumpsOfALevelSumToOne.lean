import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PartitionCubes.LevelBumpSquares
def Statement : Prop :=
  ∀ (S : RegionSequence.NestedRegions) (K m M R₁ : ℕ), S.IsLevelUnitChain K m M R₁ →
    ∀ n ≤ topLevel S, ∀ x : S.Point,
      ∑ᶠ Q ∈ {Q : LevelCube S M | Q.level = n}, Q.productBump x ^ 2 = 1
end YangMills.Construction.PartitionCubes.LevelBumpSquares
