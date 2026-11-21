import YangMills.Construction.HullsInEveryVolume.BandsOfADiameter
import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open HullsInEveryVolume
def bandMomentSumStatement : Prop :=
  ∀ CE : RenormalizationStepParameters.ParameterAssignment → ℝ, (∀ P, 0 ≤ CE P) → EventuallyInParameters fun P _ y => ∀ g : ℝ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ (β : ℝ) (K m : ℕ) (T : WeightedResponses.StageTower (P.stepParameters y)) (u n : ℕ) [NeZero n],
      HullChainAtLevel P y g β K m T u n →
      (∀ i, 2 ≤ holderExponentAtBand P.side (stageRange T u) i) ∧ ∀ (k I : ℕ) (q : ℕ → ℝ), 1 ≤ k →
        (∀ i, q i ≤ ((P.side : ℝ) * (16 * (2 ^ i * (stageRange T u : ℝ)) + 40 * (stageRange T u : ℝ))) ^ 4) →
        ∑ i ∈ Finset.range I,
            (16 ^ (k * holderExponentAtBand P.side (stageRange T u) i) *
              ((k * holderExponentAtBand P.side (stageRange T u) i).factorial : ℝ) *
              Real.exp (CE P * Real.log (stageCoupling T u) * q i)) ^
                (1 / (holderExponentAtBand P.side (stageRange T u) i : ℝ)) *
            (Real.exp (-(hullDecayRate P * stageCoupling T u *
              (1 + dyadicDiameterFloor (stageRange T u) i / (stageRange T u : ℝ))))) ^
              (1 - 1 / (holderExponentAtBand P.side (stageRange T u) i : ℝ)) ≤
          C ^ k * (k.factorial : ℝ) ^ 6 * Real.exp (-(hullDecayRate P * stageCoupling T u / 4))
end YangMills.Construction.HullTrees
end
