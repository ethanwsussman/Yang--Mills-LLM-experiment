import YangMills.Construction.ResponseInTheExpansion.DilationOfTheColdLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
def dilationRemainderLocalityBound (P : YangMills.Construction.ColdStepAtMirrorFrames.StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), P.coupling ≤ x →
    IsRegularFamily P.L t P.n₀ P.σ P.decayRate P.E P.energyRatio f → ∃ C : ℝ,
    ∀ (F : BlockFrame) (V V' : F.GaugeField F.top) (Y : F.Cell) (q : ℕ), IsCubicTopTorus P.L t P.n₀ F →
      IsSmallCurvature (5 / 4 * P.σ) V → IsSmallCurvature (5 / 4 * P.σ) V' →
      AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q →
      |(coldHalfLawAt P x f).dilationRemainder Y V - (coldHalfLawAt P x f).dilationRemainder Y V'| ≤
        C * Real.exp (-(P.κ * q / 2 ^ 7))
def dilationRemainderLocalityStatement : Prop := EventuallyInParameters dilationRemainderLocalityBound
end YangMills.Construction.WeightedResponses
end
