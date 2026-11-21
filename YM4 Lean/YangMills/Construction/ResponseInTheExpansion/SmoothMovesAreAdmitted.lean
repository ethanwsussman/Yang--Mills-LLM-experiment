import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import YangMills.Construction.ResponseInTheExpansion.MeansOfTheSmoothMoves
import YangMills.Construction.SummableBoundsOfTheFlow.ComparisonBounds
import YangMills.Construction.SummableBoundsOfTheFlow.NearPairingOfTheBox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusComparison WeightedResponses
namespace ResponseInTheExpansion
variable {F F' : BlockFrame}
structure IsComparablePair (T : StepParameters) (x : ℝ) (f : LocalFamily) (α : ℝ) (q : ℕ) (Y : F.Cell) (Y' : F'.Cell)
    {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι → ↥(chordBonds (finiteCells F)))
    (j' : ι → ↥(chordBonds (finiteCells F'))) (K : AboveFrames F) (K' : AboveFrames F') (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) : Prop where
  left_contDiffOn : ContDiffOn ℝ 1 (fun η => K η V) {η | ∀ b, ‖η b‖ < T.ballRadius}
  right_contDiffOn : ContDiffOn ℝ 1 (fun η => K' η V') {η | ∀ b, ‖η b‖ < T.ballRadius}
  comparison : ComparisonHypotheses T.ballRadius T.chainParams.lam x T.κ α T.p T.blockIndex q Y Y' j j'
    ((coldHalfLawAt T x f).exponent V) (fun η => K η V) ((coldHalfLawAt T x f).exponent V') (fun η => K' η V')
def SmoothIncrementsComparableAt (T : StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (Y : F.Cell) (Y' : F'.Cell) (q : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F'))),
    IsAdmissibleAt T t x f F V → IsAdmissibleAt T t x f F' V' →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → IsShortPairing Y Y' q j j' →
    IsComparablePair T x f (C * x ^ (-(1 / 2) : ℝ)) q Y Y' j j' ((coldHalfLawAt T x f).blockIncrement Y)
      ((coldHalfLawAt T x f).blockIncrement Y') V V' ∧
    IsComparablePair T x f C q Y Y' j j' ((coldHalfLawAt T x f).linearBlockPart Y)
      ((coldHalfLawAt T x f).linearBlockPart Y') V V' ∧
    ∀ (i : Fin 4) (back : Bool), IsComparablePair T x f (C * x ^ (-(1 / 2) : ℝ)) q Y Y' j j'
      ((coldHalfLawAt T x f).scoreRemainderIncrement (cellBond Y i back))
      ((coldHalfLawAt T x f).scoreRemainderIncrement (cellBond Y' i back)) V V'
def WeightedIncrementsComparableAt (T : StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V V' : F.GaugeField F.top) (Y : F.Cell) (q : ℕ) (ι : Type)
    [Fintype ι] [DecidableEq ι] (j j' : ι → ↥(chordBonds (finiteCells F))) (w : F.Site F.depth → ℝ) (B : ℝ),
    IsAdmissibleAt T t x f F V → IsAdmissibleAt T t x f F V' →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → IsShortPairing Y Y q j j' → 0 < B → (∀ y, |w y| ≤ B) →
    IsComparablePair T x f (C * B * x ^ (-(1 / 2) : ℝ)) q Y Y j j' ((coldHalfLawAt T x f).weightedShareIncrement w Y)
      ((coldHalfLawAt T x f).weightedShareIncrement w Y) V V'
def smoothIncrementsComparableStatement : Prop :=
  ∃ C : StepParameters → ℝ, (∀ T, 0 ≤ C T) ∧
    EventuallyInParameters fun T => SmoothIncrementsComparableAt T (C (parametersBeforeSide T)) ∧
      WeightedIncrementsComparableAt T (C (parametersBeforeSide T))
end ResponseInTheExpansion
end YangMills.Construction
end
