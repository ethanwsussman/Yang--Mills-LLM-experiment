import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import YangMills.Construction.RegionSequence.PastLastLevel
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
open YangMills.Construction.Torus YangMills.Construction.RegionSequence
open YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.PositionByType
variable {S : RegionSequence.NestedRegions} {M : ℕ}
structure FirstTypePosition (Q : LevelCube S M) : Prop where
  dichotomy : (Q.enlarge 2 ∩ S.Ω (Q.level + 1) = ∅ ∧ 1 ≤ Q.level) ∨
    (Q.enlarge 2 ∩ S.Ω (Q.level + 1)).Nonempty
  enlarge_subset : (Q.enlarge 2 ∩ S.Ω (Q.level + 1)).Nonempty → Q.enlarge 3 ⊆ S.Ω Q.level
  cubeSide_le_side : (Q.enlarge 2 ∩ S.Ω (Q.level + 1)).Nonempty →
    26 * cubeSide S M Q.level ≤ S.side
  disjoint_two_up : Q.enlarge 3 ∩ S.Ω (Q.level + 2) = ∅
  far_from_outside : ENNReal.ofReal ((M : ℝ) * S.ξ) <
    supSetDist (Q.thicken (5 / 6)) (S.cubeComplementAt 0 (S.Ω 0))
variable (S M)
structure Position : Prop where
  firstType : ∀ Q : LevelCube S M, Q.IsFirstType → FirstTypePosition Q
  secondType : ∀ Q : LevelCube S M, Q.IsSecondType →
    ENNReal.ofReal (2 * (M : ℝ) * S.ξ) ≤ supSetDist Q.pts (S.Ω 1)
def Statement : Prop :=
  ∀ (K m M R₁ : ℕ) (S : RegionSequence.NestedRegions), S.IsLevelUnitChain K m M R₁ →
    S.L ^ 5 ≤ M → Position S M
end YangMills.Construction.PartitionCubes.PositionByType
