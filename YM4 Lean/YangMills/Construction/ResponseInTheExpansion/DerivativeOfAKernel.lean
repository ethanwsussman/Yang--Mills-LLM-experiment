import YangMills.Construction.ResponseInTheExpansion.ScoresOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusLumps TorusFields StepCosts
def KernelHasCouplingDerivative : Prop :=
  ∀ (p : StepParameters), p.Admissible → ∀ (x : ℝ) (n : ℕ) [NeZero n] (b : BaseChoice p.side n) (c : TorusBond n)
    (W : TorusField (n * p.side)) (V : TorusField n),
    HasDerivAt (fun X => bondKernelAt p X W V b c) (-p.coupling * bondScore p x W V b c * bondKernelAt p x W V b c) x
end YangMills.Construction.WeightedResponses
end
