import YangMills.Construction.ClusterExpansionOfAStep.GaugeCarriesTheKernel
import YangMills.Construction.ResponseInTheExpansion.DerivativeOfAKernel
import YangMills.Construction.ResponseInTheExpansion.ScoreIsGaugeInvariant
import YangMills.Construction.ResponseInTheExpansion.SizeOfAKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses TorusLumps TorusFields StepCosts
theorem bondScoreGaugeInvariant_holds (hD : KernelHasCouplingDerivative) (hZ : BondKernelBounds)
    (hG : KernelGaugeInvariance) : BondScoreGaugeInvariantStatement := by
  intro ℓ hfit x n _ g W V b c hb
  have ha : ℓ.coupling ≠ 0 := by
    have := hfit.a_ge
    linarith
  have hk : ∀ X : ℝ, bondKernelAt ℓ X (gaugeTransform (fun z => g (parentBlock ℓ.side z)) W)
      (gaugeTransform g V) b c = bondKernelAt ℓ X W V b c := fun X =>
    ((hG ℓ hfit n g W V).2.2 X).1 b hb (torusSiteInFrame (stepBlockFrame ℓ.side n) 1 c.1, c.2)
  have h1 := hD ℓ hfit x n b c (gaugeTransform (fun z => g (parentBlock ℓ.side z)) W) (gaugeTransform g V)
  have h2 := hD ℓ hfit x n b c W V
  have he : (fun X => bondKernelAt ℓ X (gaugeTransform (fun z => g (parentBlock ℓ.side z)) W)
      (gaugeTransform g V) b c) = fun X => bondKernelAt ℓ X W V b c := funext hk
  rw [he] at h1
  have h3 := h1.unique h2
  rw [hk x] at h3
  have hpos := (hZ ℓ x n W V b c).1
  have h4 : -ℓ.coupling * bondKernelAt ℓ x W V b c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr ha) hpos.ne'
  have h5 : (-ℓ.coupling * bondKernelAt ℓ x W V b c) *
      bondScore ℓ x (gaugeTransform (fun z => g (parentBlock ℓ.side z)) W) (gaugeTransform g V) b c =
      (-ℓ.coupling * bondKernelAt ℓ x W V b c) * bondScore ℓ x W V b c := by
    linarith [h3]
  exact mul_left_cancel₀ h4 h5
end YangMills.Construction.ResponseInTheExpansion
end
