import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open Torus
namespace PartitionCubes.OutsideDistanceAndCutoffs
def Claim : Prop :=
  ∀ (S : RegionSequence.NestedRegions) (K m M R₁ : ℕ), S.IsLevelUnitChain K m M R₁ →
    ∀ n, 1 ≤ n → n ≤ S.s + 1 →
      (S.Ω n ≠ univ → ∀ x x' : S.Point,
        distToOutside S n x ≠ ⊤ ∧
          |(distToOutside S n x).toReal - (distToOutside S n x').toReal| ≤
            supNorm (x - x')) ∧
      (∀ x, distToOutside S n x < ENNReal.ofReal (mollifyRadius S M n) →
        levelTransition S M n x = 0) ∧
      (∀ x, ENNReal.ofReal (2 * mollifyRadius S M n) ≤ distToOutside S n x →
        levelTransition S M n x = 1) ∧
      (∀ x, sinCutoff S M n x ^ 2 + cosCutoff S M n x ^ 2 = 1) ∧
      tsupport (sinCutoff S M n) ⊆
        {x | ENNReal.ofReal (mollifyRadius S M n) ≤ distToOutside S n x} ∧
      (∀ x, ENNReal.ofReal (2 * mollifyRadius S M n) ≤ distToOutside S n x →
        sinCutoff S M n x = 1 ∧ cosCutoff S M n x = 0) ∧
      tsupport (cosCutoff S M n) ⊆
        {x | distToOutside S n x ≤ ENNReal.ofReal (2 * mollifyRadius S M n)}
end PartitionCubes.OutsideDistanceAndCutoffs
end YangMills.Construction
