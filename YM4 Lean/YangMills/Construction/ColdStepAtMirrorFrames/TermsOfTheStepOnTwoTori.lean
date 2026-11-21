import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.CommonBondsOfTwoTori
import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.MeansFrozenInValue
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
variable {F F' : BlockFrame}
def IsCloseOnTwoTori (ρ x κ ε : ℝ) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ)
    (θ : F.Cell → StepVariable (finiteCells F) → ℝ) (θ' : F'.Cell → StepVariable (finiteCells F') → ℝ)
    (H : StepVariable (finiteCells F) → ℝ) (H' : StepVariable (finiteCells F') → ℝ) : Prop :=
  IsCloseInValue ρ x κ ε (chordBondCell F) (cellDistReal F) (commonBondLeft Y Y' (r / 2))
    (commonBondRight Y Y' (r / 2)) (offsetCell Y (r / 8)) (offsetCell Y' (r / 8)) θ θ' H H' Y
def StepTermsCloseAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F F' : BlockFrame) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (star : Bool) (v : ℝ), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsCubicTopTorus T.L t T.n₀ F' →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r → T.blockIndex ≤ r → 0 ≤ v → v ≤ 1 →
    IsCloseOnTwoTori T.ballRadius x T.κ (T.Ct * Real.exp (-(2 * T.κ * r))) Y Y' r
      (fun Z η => v * cellExponent star T.a T.chainParams.ρA x (frameRadius x) Z V η +
        (1 - v) * cellQuadratic T.chainParams.lam x Z η)
      (fun Z η => v * cellExponent star T.a T.chainParams.ρA x (frameRadius x) Z V' η +
        (1 - v) * cellQuadratic T.chainParams.lam x Z η)
      (fun η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y V η -
        cellQuadratic T.chainParams.lam x Y η)
      (fun η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Y' V' η -
        cellQuadratic T.chainParams.lam x Y' η) ∧
    IsCloseOnTwoTori T.ballRadius x T.κ (T.Ct * (1 + T.energyRatio) * Real.exp (-(2 * T.κ * r))) Y Y' r
      (fun Z η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Z V η -
        v * cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Z η V)
      (fun Z η => cellExponent star T.a T.chainParams.ρA x (frameRadius x) Z V' η -
        v * cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Z η V')
      (fun η => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y η V)
      (fun η => cellCentredExpansion star T.a T.chainParams.ρA (frameRadius x) f Y' η V')
def StepTermsCloseOnTwoTori : Prop := EventuallyInParameters StepTermsCloseAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
