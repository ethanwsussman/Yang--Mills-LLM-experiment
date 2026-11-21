import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import YangMills.Construction.ResponseInTheExpansion.SlotsOfTheColdLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def SecondOrderSlotMeanAt (T : StepParameters) (Cq : ℕ → ℝ) (B : ℝ) : Prop :=
  ∀ (t : ℕ) (x h : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell)
    (K : AboveFrames F),
    IsAdmissibleAt T t x f F V → IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → 0 < h →
    IsSmoothBoundedSlot (coldHalfLawAt T x f) Cq 2 h Y K V →
      (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
        ContDiffAt ℝ 2 (fun τ : Fin k → ℝ =>
          (coldHalfLawAt T x f).expectationOf K (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0) ∧
      ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 2 →
        AreUnitVectors X →
        |bondDeriv ((coldHalfLawAt T x f).expectationOf K) V c X -
            (coldHalfLawAt T x f).expectation V (fun η => bondDeriv (K η) V c X)| ≤
          B * h * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c))
def secondOrderSlotMeanStatement : Prop :=
  ∀ Cq : StepParameters → ℕ → ℝ, (∀ T q, 0 ≤ Cq T q) → ∃ B : StepParameters → ℝ, (∀ T, 0 ≤ B T) ∧
    EventuallyInParameters fun T =>
      SecondOrderSlotMeanAt T (Cq (parametersBeforeSide T)) (B (parametersBeforeSide T))
def IsSecondOrderRemainder (T : StepParameters) (x : ℝ) (f : LocalFamily) (Cq : ℕ → ℝ) (C h : ℝ)
    (Y : F.Cell) (K : AboveFrames F) (V : F.GaugeField F.top) : Prop :=
  IsSmoothBoundedSlot (coldHalfLawAt T x f) Cq 2 h Y K V ∧
    MeasureTheory.Integrable (fun η => K η V *
      ballDensity (coldHalfLawAt T x f).radialWeight ((coldHalfLawAt T x f).exponent V) η) ∧
    ∀ (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions), AreUnitVectors X →
      |(coldHalfLawAt T x f).expectation V (fun η => bondDeriv (K η) V c X)| ≤
        C * h * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c))
end YangMills.Construction.WeightedResponses
end
