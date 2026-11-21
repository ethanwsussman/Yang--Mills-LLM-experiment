import YangMills.Construction.ResponseInTheExpansion.JointLawOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepCosts BlockAverages
def bondScoreVariance (p : StepParameters) (x : ℝ) {n : ℕ} [NeZero n] (W : TorusField (n * p.side))
    (b : BaseChoice p.side n) (c : TorusBond n) : ℝ :=
  (∫ g : UnitQuaternion, bondScore p x W (fieldAtBond (trivialField n) c g) b c ^ 2 *
      bondKernelAt p x W (fieldAtBond (trivialField n) c g) b c ∂haarUnit) -
    (∫ g : UnitQuaternion, bondScore p x W (fieldAtBond (trivialField n) c g) b c *
      bondKernelAt p x W (fieldAtBond (trivialField n) c g) b c ∂haarUnit) ^ 2
def ScoreSumCovariance : Prop :=
  ∀ (p : StepParameters), p.Admissible → ∀ (x : ℝ) (n : ℕ) [NeZero n] (W : TorusField (n * p.side))
    (v v' : TorusBond n → ℝ),
    ∑ b : BaseChoice p.side n, ∫ V : TorusField n, (∑ c : TorusBond n, v c * bondScore p x W V b c) *
        (∑ c : TorusBond n, v' c * bondScore p x W V b c) * stepTransitionDensity p x W b V ∂(fieldHaar n) =
      ∑ c : TorusBond n, v c * v' c * ∑ b : BaseChoice p.side n, ∫ V : TorusField n,
        bondScoreVariance p x W b c * stepTransitionDensity p x W b V ∂(fieldHaar n)
end YangMills.Construction.WeightedResponses
end
