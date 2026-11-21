import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import YangMills.Construction.ResponseInTheExpansion.SlotsOfTheColdLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def slotThirdOrderCovarianceAt (T : StepParameters) (Cq : ℕ → ℝ) (B : ℝ) : Prop :=
  ∀ (t : ℕ) (x h : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell)
    (K : AboveFrames F) (c : Fin 3 → F.Site F.top × Fin 4) (X : Fin 3 → imaginaryQuaternions),
    IsAdmissibleAt T t x f F V →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → 0 < h →
    IsSlot (coldHalfLawAt T x f) Cq h Y K V → AreUnitVectors X →
    |(coldHalfLawAt T x f).covariance V (fun η => K η V)
        (fun η => bondDeriv (fun V' => (coldHalfLawAt T x f).exponent V' η) V c X)| ≤
      B * h * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c))
def slotThirdOrderCovarianceStatement : Prop :=
  ∀ Cq : StepParameters → ℕ → ℝ, (∀ T q, 0 ≤ Cq T q) → ∃ B : StepParameters → ℝ, (∀ T, 0 ≤ B T) ∧
    EventuallyInParameters fun T =>
      slotThirdOrderCovarianceAt T (Cq (sizeParameters T)) (B (parametersBeforeSide T))
end YangMills.Construction.WeightedResponses
end
