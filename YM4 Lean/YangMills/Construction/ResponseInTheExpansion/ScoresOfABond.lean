import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace WeightedResponses
open TorusFields TorusLumps StepCosts BlockAverages LumpContours
variable {n : ℕ}
def fieldAtBond (V : TorusField n) (c : TorusBond n) (g : UnitQuaternion) : TorusField n :=
  Function.update V c.1 (Function.update (V c.1) c.2 g)
def bondKernelAt (ℓ : StepParameters) (x : ℝ) (W : TorusField (n * ℓ.side)) (V : TorusField n)
    (b : BaseChoice ℓ.side n) (c : TorusBond n) : ℝ :=
  bondKernel ℓ x (readAtLevel (stepBlockFrame ℓ.side n) 0 W) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b
    (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)
def fitConditionalMean (ℓ : StepParameters) (x : ℝ) (W : TorusField (n * ℓ.side)) (b : BaseChoice ℓ.side n)
    (c : TorusBond n) : ℝ :=
  ∫ g : UnitQuaternion, bondFit ℓ W (fieldAtBond (trivialField n) c g) b c *
    bondKernelAt ℓ x W (fieldAtBond (trivialField n) c g) b c ∂haarUnit
def bondScore (ℓ : StepParameters) (x : ℝ) (W : TorusField (n * ℓ.side)) (V : TorusField n)
    (b : BaseChoice ℓ.side n) (c : TorusBond n) : ℝ :=
  bondFit ℓ W V b c - fitConditionalMean ℓ x W b c
end WeightedResponses
end YangMills.Construction
end
