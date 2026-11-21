import YangMills.Construction.ResponseInTheExpansion.ScoresOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields TorusLumps StepCosts
def BondKernelBounds : Prop :=
  ∀ (p : StepParameters) (x : ℝ) (n : ℕ) [NeZero n] (W : TorusField (n * p.side)) (V : TorusField n)
    (b : BaseChoice p.side n) (c : TorusBond n),
    0 < bondKernelAt p x W V b c ∧ bondKernelAt p x W V b c ≤ Real.exp (2 * |p.coupling * x|)
end YangMills.Construction.WeightedResponses
end
