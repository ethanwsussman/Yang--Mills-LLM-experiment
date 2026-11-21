import YangMills.Construction.ResponseInTheExpansion.DilationOfTheColdLaw
import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open BlockAverages ColdStepAtMirrorFrames
def CutoffTermExpectationAt (T : StepParameters) (B : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell),
    IsAdmissibleAt T t x f F V → IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    MeasureTheory.Integrable (fun η => (coldHalfLawAt T x f).cutoffTerm Y η V *
      ballDensity (coldHalfLawAt T x f).radialWeight ((coldHalfLawAt T x f).exponent V) η) ∧
    (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun τ : Fin k → ℝ =>
        (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).cutoffTerm Y)
          (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0) ∧
    ∀ (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions), AreUnitVectors X →
      |bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).cutoffTerm Y)) V c X| ≤
        B * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c))
def cutoffTermExpectationStatement : Prop :=
  ∃ B : StepParameters → ℝ, (∀ T, 0 ≤ B T) ∧
    EventuallyInParameters fun T => CutoffTermExpectationAt T (B (parametersBeforeSide T))
end YangMills.Construction.WeightedResponses
end
