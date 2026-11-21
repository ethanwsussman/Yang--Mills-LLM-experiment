import YangMills.Construction.ClusterExpansionOfAStep.CumulantsOfTheKernelsAtMovedBonds
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
open MeasureTheory
namespace YangMills.Construction
open BlockAverages LumpContours TorusFields
namespace TorusLumps
def kernelMass (p : StepParameters) (x : ℝ) {n : ℕ} [NeZero n] {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (ρ : Ξ → ENNReal) (W : Ξ → (stepBlockFrame p.side n).GaugeField 0)
    (b : Ξ → (stepBlockFrame p.side n).Cell → (stepBlockFrame p.side n).Site 0)
    (V : TorusField n) : ℝ :=
  (∫⁻ ξ, ρ ξ * ENNReal.ofReal (∏ c : (stepBlockFrame p.side n).Cell × Fin 4,
    bondKernel p x (W ξ) (readAtLevel (stepBlockFrame p.side n) 1 V) (b ξ) c) ∂μ).toReal
def KernelMassCumulantBound : Prop :=
  ∀ (p : StepParameters) (x : ℝ) (n : ℕ) [NeZero n] (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ)
    (ρ : Ξ → ENNReal) (W : Ξ → (stepBlockFrame p.side n).GaugeField 0)
    (b : Ξ → (stepBlockFrame p.side n).Cell → (stepBlockFrame p.side n).Site 0) (V : TorusField n),
    1 ≤ p.coupling * x → Measurable ρ →
    (∀ c : (stepBlockFrame p.side n).Cell × Fin 4, MeasurableQuaternion fun ξ =>
      contourMean p.baseDepth
        (hotLumps p.grid p.threshold (levelSites (stepBlockFrame p.side n) 0) (W ξ)) (b ξ) (W ξ) c) →
    (∀ (V' : TorusField n) (c : (stepBlockFrame p.side n).Cell × Fin 4), Measurable fun ξ =>
      bondKernel p x (W ξ) (readAtLevel (stepBlockFrame p.side n) 1 V') (b ξ) c) →
    0 < kernelMass p x μ ρ W b V →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiff ℝ ∞ (fun t : Fin k → ℝ => kernelMass p x μ ρ W b (perturb c X t V)) ∧
      (1 ≤ k → k ≤ 3 → AreUnitVectors X →
        |mixedDeriv (fun V' => Real.log (kernelMass p x μ ρ W b V')) V c X| ≤
          (32 * (p.coupling * x)) ^ k)
end TorusLumps
end YangMills.Construction
end
