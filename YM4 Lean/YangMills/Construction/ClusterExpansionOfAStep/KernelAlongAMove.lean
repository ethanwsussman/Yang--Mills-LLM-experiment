import YangMills.Construction.ClusterExpansionOfAStep.LumpsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.KernelVariation
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
def kernelAlongPerturbation (ℓ : StepParameters) (x : ℝ) {n : ℕ} [NeZero n]
    (W : (stepBlockFrame ℓ.side n).GaugeField 0) (V : TorusField n) {k : ℕ}
    (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) : ℝ :=
  averagedKernel ℓ x W (readAtLevel (stepBlockFrame ℓ.side n) 1 (perturb c X τ V))
def KernelAlongPerturbationBounds : Prop :=
  ∃ Cp : ℝ, 1 ≤ Cp ∧ ∀ (ℓ : StepParameters) (x : ℝ), 1 ≤ ℓ.coupling → 1 ≤ x → ∀ (n : ℕ) [NeZero n]
    (W : (stepBlockFrame ℓ.side n).GaugeField 0) (V : TorusField n) (k : ℕ) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions), AreUnitVectors X →
    ContDiff ℝ 40 (kernelAlongPerturbation ℓ x W V c X) ∧ (∀ τ, 0 ≤ kernelAlongPerturbation ℓ x W V c X τ) ∧
    (∀ τ, ∀ i ≤ 40, ‖iteratedFDeriv ℝ i (kernelAlongPerturbation ℓ x W V c X) τ‖ ≤
      (Cp * (ℓ.coupling * x) * ((k : ℝ) + 1) ^ 2) ^ i * kernelAlongPerturbation ℓ x W V c X τ) ∧
    ∀ τ, kernelAlongPerturbation ℓ x W V c X τ ≤
      Real.exp (2 * (ℓ.coupling * x) * k) * kernelAlongPerturbation ℓ x W V c X 0
end YangMills.Construction.KernelVariation
end
