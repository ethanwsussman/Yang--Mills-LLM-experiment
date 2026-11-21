import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import YangMills.Construction.ResponseInTheExpansion.SlotsOfTheColdLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def SlotExpectationDerivAt (T : StepParameters) (Cq : ℕ → ℝ) (B : ℝ) : Prop :=
  ∀ (t : ℕ) (x h : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell) (K : AboveFrames F),
    IsAdmissibleAt T t x f F V → IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → 0 < h →
    IsSlot (coldHalfLawAt T x f) Cq h Y K V →
      ContDiffThreeAlongBonds ((coldHalfLawAt T x f).expectationOf K) V ∧
      ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
        AreUnitVectors X →
        |bondDeriv ((coldHalfLawAt T x f).expectationOf K) V c X -
            (coldHalfLawAt T x f).expectation V (fun η => bondDeriv (K η) V c X)| ≤
          B * h * Real.exp (-(T.κ / 2 ^ 5 * bondSpan Y c))
def slotExpectationDerivStatement : Prop :=
  ∀ Cq : StepParameters → ℕ → ℝ, (∀ T q, 0 ≤ Cq T q) → ∃ B : StepParameters → ℝ, (∀ T, 0 ≤ B T) ∧
    EventuallyInParameters fun T => SlotExpectationDerivAt T (Cq (sizeParameters T)) (B (parametersBeforeSide T))
end YangMills.Construction.WeightedResponses
end
