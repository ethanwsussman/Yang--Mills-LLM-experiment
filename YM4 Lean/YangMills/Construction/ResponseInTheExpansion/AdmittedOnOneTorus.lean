import YangMills.Construction.ResponseInTheExpansion.SmoothMovesAreAdmitted
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames WeightedResponses Interpolation TorusComparison
namespace ResponseInTheExpansion
def IsComparableOnOneTorus (T : StepParameters) (t : ℕ) (x : ℝ) (f : LocalFamily)
    (K : ∀ F : BlockFrame, F.Cell → AboveFrames F) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : BlockFrame) (V V' : F.GaugeField F.top) (Y : F.Cell) (q : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F))), IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → IsSmallCurvature (5 / 4 * T.σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → IsShortPairing Y Y q j j →
    IsComparablePair T x f C q Y Y j j (K F Y) (K F Y) V V'
end ResponseInTheExpansion
end YangMills.Construction
end
