import YangMills.Construction.ColdStepAtMirrorFrames.ComparisonOfPartsBetween
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.Interpolation
namespace YangMills.Construction.ColdStepAtMirrorFrames
def InterpolatedSlopesCompareAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x s : ℝ) (h : LocalFamily) (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (Y : F.Cell) (Y' : F'.Cell) (q : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F'))) (o : Fin 4 → ℤ),
    InterpolatedComparisonSetting T t x s h V V' Y Y' q j j' o →
    PairedPartsCompareSmoothly T.ballRadius (T.Ct / 3) (Real.exp (-(4 * T.κ * q))) x T.κ j j'
      (Y + siteOfCoords F.top o)
      (interpolatedSlopePart s T.a T.chainParams.ρA x (frameRadius x) (Y + siteOfCoords F.top o) V)
      (interpolatedSlopePart s T.a T.chainParams.ρA x (frameRadius x) (Y' + siteOfCoords F'.top o) V')
def interpolatedSlopesCompareStatement : Prop := EventuallyInParameters InterpolatedSlopesCompareAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
