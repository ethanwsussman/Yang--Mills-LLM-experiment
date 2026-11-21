import YangMills.Construction.ResponseInTheExpansion.DilationOfTheColdLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
def dilationRemainderSecondOrderBound (P : YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell),
    IsAdmissibleAt P t x f F V →
    IsRegularFamily P.L t P.n₀ P.σ P.decayRate P.E P.energyRatio f →
    (∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      ContDiffAt ℝ 2 (fun τ : Fin k → ℝ => (coldHalfLawAt P x f).dilationRemainder Y (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) 0) ∧
    (∀ (c c' : F.Site F.top × Fin 4) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
      |bondDeriv ((coldHalfLawAt P x f).dilationRemainder Y) V ![c, c'] ![X, X']| ≤
        P.CE * x ^ (-(3 / 2) : ℝ) * Real.exp (-(P.κ / 2 ^ 5 * bondSpan Y ![c, c']))) ∧
    ∀ (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions), ‖X‖ = 1 →
      bondDeriv ((coldHalfLawAt P x f).dilationRemainder Y) (flatTopField (F := F)) ![c] ![X] = 0
def dilationRemainderSecondOrderStatement : Prop := EventuallyInParameters dilationRemainderSecondOrderBound
end YangMills.Construction.WeightedResponses
end
