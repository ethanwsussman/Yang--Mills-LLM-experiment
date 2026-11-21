import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.TorusFields
def KernelImageGaugeInvariant : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (x : ℝ) (D : TorusFunctional) (n : ℕ) [NeZero n],
    (∀ (γ : TorusSite (n * ℓ.side) → YangMills.Construction.BlockAverages.UnitQuaternion)
      (W : TorusField (n * ℓ.side)),
      D (n * ℓ.side) (gaugeTransform γ W) = D (n * ℓ.side) W) →
    ∀ (g : TorusSite n → YangMills.Construction.BlockAverages.UnitQuaternion) (V : TorusField n),
      kernelImage ℓ x D n (gaugeTransform g V) = kernelImage ℓ x D n V
end YangMills.Construction.TorusLumps
end
