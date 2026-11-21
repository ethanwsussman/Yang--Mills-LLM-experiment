import YangMills.Construction.ResponseInTheExpansion.ResponsesOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusLumps TorusFields BlockAverages WeightedResponses
def coldResponseGaugeInvariantStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters), ℓ.Admissible → ∀ (β : ℝ) (x al : ℕ → ℝ) (t n : ℕ) [NeZero n]
    (y : TorusSite n) (g : TorusSite n → UnitQuaternion) (W : TorusField n)
    (h : PlaquetteWeight (fineSide ℓ.side t n)),
    coldResponseChain ℓ β x al t n y (gaugeTransform g W) h = coldResponseChain ℓ β x al t n y W h
end YangMills.Construction.ResponseInTheExpansion
end
