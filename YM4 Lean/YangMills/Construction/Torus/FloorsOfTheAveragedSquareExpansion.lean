import YangMills.Construction.Conventions.PositiveConstant
import YangMills.Construction.Weighted.ChainSiteSums
import YangMills.Construction.Weighted.ExpDecayInverse
import YangMills.Construction.Weighted.InverseExpansionConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted.ExpansionFloors
def ConstantsDependence : Prop :=
  Conventions.DependsOnlyThrough
      (fun q : ℕ × ℕ × ℝ =>
        (inverseExpansionRate q.1 q.2.1, expansionDecayRate q.1 q.2.1,
          expansionSeparationFloor q.1 q.2.1))
      (fun q => (q.1, q.2.1)) ∧
    Conventions.DependsOnlyThrough
      (fun q : ℕ × ℕ × ℝ =>
        (expansionConstFirst q.1 q.2.1 q.2.2, expansionConstSecond q.1 q.2.1 q.2.2,
          expansionBlockSizeFloor q.1 q.2.1 q.2.2, expansionConstBound q.1 q.2.1 q.2.2))
      id
def ConstantsOrder (L : ℕ) : Prop :=
  0 < 2 * expansionDecayRate 4 L ∧
    2 * expansionDecayRate 4 L ≤ inverseExpansionRate 4 L ∧
    expansionDecayRate 4 L ≤ 1 / 32 * greenDecayRate 4 L ∧
    (∀ c : ℝ, 1 ≤ c → 6 * (L : ℝ) ≤ expansionBlockSizeFloor 4 L c) ∧
    inverseExpansionRate 4 L =
      decayRateOfInverse L (lowerBoundConst 4) (1 / 2 * greenDecayRate 4 L) (upperBoundConst 4 L)
def FloorConsequences (D : TorusData) : Prop :=
  8 * (4 * Real.log (D.L : ℝ) + 1) / greenDecayRate 4 D.L ≤
      (D.gapNumber : ℝ) * (D.blockNumber : ℝ) ∧
    32 * (4 * Real.log (D.L : ℝ) + 1) / greenDecayRate 4 D.L ≤
      (D.gapNumber : ℝ) * (D.blockNumber : ℝ) ∧
    4 * (4 * Real.log (D.L : ℝ) + 1) / (1 / 2 * greenDecayRate 4 D.L) ≤
      (D.gapNumber : ℝ) * (D.blockNumber : ℝ) ∧
    (∀ κ : ℝ, 1 / 2 * expansionDecayRate 4 D.L ≤ κ →
      latticeSumRadius 4 D.L κ ≤ (D.gapNumber : ℝ) * (D.blockNumber : ℝ)) ∧
    4 * D.scaleRatioRate ≤ 1 / 2 * expansionDecayRate 4 D.L ∧
    1 / 2 * expansionDecayRate 4 D.L ≤ 1 / 4 * greenDecayRate 4 D.L
def Statement : Prop :=
  ConstantsDependence ∧
    (∀ L : ℕ, Blocking.FourDimOddFactor 4 L → ConstantsOrder L) ∧
    ∀ D : TorusData, expansionSeparationFloor 4 D.L ≤ (D.gapNumber : ℝ) * (D.blockNumber : ℝ) →
      FloorConsequences D
end YangMills.Construction.Weighted.ExpansionFloors
