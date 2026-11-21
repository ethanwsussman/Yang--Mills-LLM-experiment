import YangMills.Construction.ResponseInTheExpansion.ScoresOfABond
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps StepCosts BlockAverages WeightedResponses
def BondScoreGaugeInvariantStatement : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (x : ℝ) (n : ℕ) [NeZero n] (g : TorusSite n → UnitQuaternion)
    (W : TorusField (n * ℓ.side)) (V : TorusField n) (b : BaseChoice ℓ.side n) (c : TorusBond n),
    b ∈ baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) →
    bondScore ℓ x (gaugeTransform (fun z => g (parentBlock ℓ.side z)) W) (gaugeTransform g V) b c = bondScore ℓ x W V b c
end YangMills.Construction.ResponseInTheExpansion
end
