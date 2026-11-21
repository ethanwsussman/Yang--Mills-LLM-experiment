import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.CubesAndCutoffs
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PartitionCubes
def PartitionFnSupportStatement : Prop :=
  ∀ (S : RegionSequence.NestedRegions) (K m M R₁ : ℕ), S.IsLevelUnitChain K m M R₁ →
    ∀ Q : LevelCube S M,
      Q.supp ⊆
          {x | Torus.supNorm (x - Q.centre) < 2 / 3 * cubeSide S M Q.level} ∩
            {x | Q.level ≠ 0 →
              ENNReal.ofReal (mollifyRadius S M Q.level) ≤ distToOutside S Q.level x} ∩
            {x | distToOutside S (Q.level + 1) x ≤
              ENNReal.ofReal (2 * mollifyRadius S M (Q.level + 1))} ∧
        ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
          Q.thicken s ⊆ {x | Torus.supNorm (x - Q.centre) < 5 / 6 * cubeSide S M Q.level}
end YangMills.Construction.PartitionCubes
end
