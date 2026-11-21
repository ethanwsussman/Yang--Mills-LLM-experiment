import YangMills.Construction.ClusterExpansionOfAStep.LumpsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.TorusFields
def MeasurableQuaternion {Ξ : Type} [MeasurableSpace Ξ] (f : Ξ → ℍ[ℝ]) : Prop :=
  Measurable (fun ξ => (f ξ).re) ∧ Measurable (fun ξ => (f ξ).imI) ∧
    Measurable (fun ξ => (f ξ).imJ) ∧ Measurable (fun ξ => (f ξ).imK)
def kernelProductMean (ℓ : StepParameters) (x : ℝ) {n : ℕ} [NeZero n] {Ξ : Type} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (A : Ξ → ℝ) (W : Ξ → (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : Ξ → (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) (V : TorusField n) : ℝ :=
  ∫ ξ, A ξ * ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
    bondKernel ℓ x (W ξ) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) (b ξ) c ∂μ
def KernelCumulantBound : Prop :=
  ∀ (ℓ : StepParameters) (x : ℝ) (n : ℕ) [NeZero n] (Ξ : Type) [MeasurableSpace Ξ] (μ : Measure Ξ)
    (A : Ξ → ℝ) (W : Ξ → (stepBlockFrame ℓ.side n).GaugeField 0)
    (b : Ξ → (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0) (V : TorusField n),
    1 ≤ ℓ.coupling * x → (∀ ξ, 0 ≤ A ξ) →
    (∀ c : (stepBlockFrame ℓ.side n).Cell × Fin 4, MeasurableQuaternion fun ξ =>
      contourMean ℓ.baseDepth
        (hotLumps ℓ.grid ℓ.threshold (levelSites (stepBlockFrame ℓ.side n) 0) (W ξ)) (b ξ) (W ξ) c) →
    Integrable (fun ξ => A ξ * ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
      bondKernel ℓ x (W ξ) (readAtLevel (stepBlockFrame ℓ.side n) 1 V) (b ξ) c) μ →
    0 < kernelProductMean ℓ x μ A W b V →
    ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions),
      ContDiff ℝ ∞ (fun σ : Fin k → ℝ => kernelProductMean ℓ x μ A W b (perturb c X σ V)) ∧
      (1 ≤ k → k ≤ 3 → AreUnitVectors X →
        |mixedDeriv (fun V' => Real.log (kernelProductMean ℓ x μ A W b V')) V c X| ≤
          (32 * (ℓ.coupling * x)) ^ k)
end YangMills.Construction.TorusLumps
end
