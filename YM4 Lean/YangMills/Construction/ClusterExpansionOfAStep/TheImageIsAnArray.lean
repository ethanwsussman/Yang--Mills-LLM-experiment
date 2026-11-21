import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open BlockAverages TorusFields
def KernelImageIsDensity : Prop :=
  ∀ (P : StepParameters), P.Admissible → ∀ (t : ℕ) (x : ℝ) (D : TorusFunctional), 0 < x →
    4 * P.n₀ + 2 ^ 16 ≤ clusterRange x →
    HasExpansion P t x D → ∀ (n : ℕ) [NeZero n], P.n₀ ≤ n →
      (∀ V : TorusField n, Integrable (fun W : TorusField (n * P.side) => D (n * P.side) W *
        averagedKernel P x (readAtLevel (stepBlockFrame P.side n) 0 W)
          (readAtLevel (stepBlockFrame P.side n) 1 V)) (fieldHaar (n * P.side))) ∧
      Measurable (kernelImage P x D n) ∧ (∀ V, 0 ≤ kernelImage P x D n V) ∧
      (∀ (g : TorusSite n → UnitQuaternion) (V : TorusField n),
        kernelImage P x D n (gaugeTransform g V) = kernelImage P x D n V) ∧
      ∀ (g : TorusIsometry) (V V' : TorusField n), g.Transports V V' →
        kernelImage P x D n V' = kernelImage P x D n V
end YangMills.Construction.TorusLumps
end
