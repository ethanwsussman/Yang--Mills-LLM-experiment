import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import Mathlib
set_option autoImplicit false
open scoped ENNReal
open YangMills.Construction.Torus
noncomputable section
namespace YangMills.Construction.PartitionCubes.DistanceSeparation
structure Holds (S : RegionSequence.NestedRegions) (M R₁ : ℕ) : Prop where
  lt_distToOutside : ∀ n < S.s, ∀ x ∈ S.Ω (n + 1),
    ENNReal.ofReal ((R₁ : ℝ) * cubeSide S M n) < distToOutside S n x
  L_le_gap : S.L ≤ R₁
  thirteen_le_L : 13 ≤ S.L
  two_mul_mollifyRadius_succ : ∀ n, 2 * mollifyRadius S M (n + 1) = cubeSide S M n / 3
  mollifyRadius_le : ∀ n, mollifyRadius S M n ≤ cubeSide S M n / 78
  mollifyRadius_mono : ∀ n, mollifyRadius S M n ≤ mollifyRadius S M (n + 1)
  scale_succ_le : ∀ n, 366 * S.scale (n + 1) ≤ mollifyRadius S M n
  exists_near_supp : ∀ (Q : LevelCube S M) (c : ℝ), 0 ≤ c → ∀ x ∈ Q.thicken c,
    ∃ y ∈ Q.supp, supNorm (x - y) ≤ c * mollifyRadius S M Q.level
def Statement : Prop :=
  ∀ (K m M R₁ : ℕ) (S : RegionSequence.NestedRegions), S.IsLevelUnitChain K m M R₁ →
    S.L ^ 5 ≤ M → Holds S M R₁
end YangMills.Construction.PartitionCubes.DistanceSeparation
