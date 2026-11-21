import YangMills.Construction.ColdStepAtMirrorFrames.PartsOfTheExponent
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def SlopeComponentsCloseAt (P : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (F F' : BlockFrame) (U : F.GaugeField F.top) (U' : F'.GaugeField F'.top)
    (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (star : Bool), AgreeingTopPair P t x U U' Y Y' r →
    NearCellsClose P.ballRadius x P.κ ((P.Ct / 4) * Real.exp (-(2 * P.κ * r))) Y Y' r
      (fun Z η => slopeComponent star P.a P.chainParams.ρA x (frameRadius x) Z U η)
      (fun Z η => slopeComponent star P.a P.chainParams.ρA x (frameRadius x) Z U' η)
def SlopeComponentsCloseOnTwoTori : Prop := EventuallyInParameters SlopeComponentsCloseAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
