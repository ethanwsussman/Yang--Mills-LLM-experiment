import YangMills.Construction.ColdStepAtMirrorFrames.PartsOfTheExponent
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def GapComponentsCloseAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell)
    (Y' : F'.Cell) (r : ℕ) (star : Bool), AgreeingTopPair T t x V V' Y Y' r →
    NearCellsClose T.ballRadius x T.κ ((T.Ct / 4) * Real.exp (-(2 * T.κ * r))) Y Y' r
      (fun Z η => kernelGapComponent star T.a T.chainParams.ρA x (frameRadius x) Z V η)
      (fun Z η => kernelGapComponent star T.a T.chainParams.ρA x (frameRadius x) Z V' η)
def gapComponentsCloseOnTwoTori : Prop := EventuallyInParameters GapComponentsCloseAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
