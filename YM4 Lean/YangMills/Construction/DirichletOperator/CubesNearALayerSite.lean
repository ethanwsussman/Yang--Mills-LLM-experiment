import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import YangMills.Construction.RegionSequence.FineLatticeNorms
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes.CubesNearShellSite
def Claim : Prop :=
  ∀ (K m M R₁ : ℕ) (S : RegionSequence.NestedRegions), S.IsLevelUnitChain K m M R₁ →
    S.L ^ 5 ≤ M →
    (∀ (j : ℕ), ∀ y ∈ S.centresAt j, ∀ Q ∈ active S M,
      (Q.supp ∩ cubeHalfSide y (4 * S.levelScale y)).Nonempty →
        Q.level + 1 = j ∨ Q.level = j) ∧
    (∀ (j : ℕ), ∀ y ∈ S.centresAt j, ∀ Q ∈ active S M,
      (Q.supp ∩ cubeHalfSide y (4 * S.levelScale y)).Nonempty →
        y ∈ Q.thicken (1 / 6)) ∧
    (∀ (j : ℕ), ∀ y ∈ S.centresAt j,
      {Q : LevelCube S M | Q ∈ active S M ∧
        (Q.supp ∩ cubeHalfSide y (4 * S.levelScale y)).Nonempty}.encard ≤ 2 ^ (4 + 1))
end PartitionCubes.CubesNearShellSite
end YangMills.Construction
