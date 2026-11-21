import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions
namespace ThickenedCubeLocation
open PartitionCubes
variable {S : RegionSequence.NestedRegions} {M : ℕ}
structure Located (Q : LevelCube S M) : Prop where
  near_centre : Q.thicken (5 / 6) ⊆
    {x | supNorm (x - Q.centre) < 5 / 6 * cubeSide S M Q.level}
  far_from_outside : 1 ≤ Q.level → Q.thicken (5 / 6) ⊆
    {x | ENNReal.ofReal (1 / 6 * mollifyRadius S M Q.level) ≤ distToOutside S Q.level x}
  near_next_outside : Q.thicken (5 / 6) ⊆
    {x | distToOutside S (Q.level + 1) x ≤
      ENNReal.ofReal (1 / 2 * cubeSide S M Q.level)}
  subset_strict : Q.thicken (5 / 6) ⊆ Q.strictPts
  subset_shells : (1 ≤ Q.level ∨ Q.pts ⊆ S.Ω 0) →
    Q.thicken (5 / 6) ⊆ S.shellOf Q.level ∪ S.shellOf (Q.level + 1)
def Claim : Prop :=
  ∀ (K m M R₁ : ℕ) (S : RegionSequence.NestedRegions), S.IsLevelUnitChain K m M R₁ →
    S.L ^ 5 ≤ M → ∀ Q ∈ active S M, Located Q
end ThickenedCubeLocation
end YangMills.Construction
