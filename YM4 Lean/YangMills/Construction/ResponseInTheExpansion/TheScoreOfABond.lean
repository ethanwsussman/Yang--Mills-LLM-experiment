import YangMills.Construction.ResponseInTheExpansion.ElementsOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepCosts BlockAverages LumpContours
def BondScoreProperties : Prop :=
  ∀ (p : StepParameters), p.Admissible → ∀ (x : ℝ) (n : ℕ) [NeZero n] (b : BaseChoice p.side n) (c : TorusBond n),
    (∀ W : TorusField (n * p.side), fitConditionalMean p x W b c =
      meanNorm p W b c * deriv logPartitionGap (p.coupling * x * meanNorm p W b c)) ∧
    (∀ (W : TorusField (n * p.side)) (V : TorusField n), bondScore p x W V b c =
      meanNorm p W b c * (deriv partitionFn (p.coupling * x * meanNorm p W b c) /
          partitionFn (p.coupling * x * meanNorm p W b c)) -
        (bondMean p (readAtLevel (stepBlockFrame p.side n) 0 W) b c *
          ((V c.1 c.2)⁻¹ : UnitQuaternion)).re) ∧
    (∀ (W : TorusField (n * p.side)) (V : TorusField n), |bondScore p x W V b c| ≤ 2) ∧
    (∀ (W : TorusField (n * p.side)) (V : TorusField n),
      ∫ g : UnitQuaternion, bondScore p x W (fieldAtBond V c g) b c *
        bondKernelAt p x W (fieldAtBond V c g) b c ∂haarUnit = 0) ∧
    Measurable fun q : TorusField (n * p.side) × TorusField n => bondScore p x q.1 q.2 b c
end YangMills.Construction.WeightedResponses
end
