import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import YangMills.Construction.ResponseInTheExpansion.MeansOfTheSmoothMoves
import YangMills.Construction.SummableBoundsOfTheFlow.NearPairingOfTheBox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open BlockAverages ColdStepAtMirrorFrames TorusComparison
variable {F F' : BlockFrame}
def weightedBondNorm {ι : Type} [Fintype ι] (κ : ℝ) (Y : F.Cell) (j : ι → ↥(chordBonds (finiteCells F)))
    (ζ : BondField ι) : ℝ :=
  ∑ i, Real.exp (-(κ * bondDistToCell Y (j i))) * ‖ζ i‖
def weightedBondNormSq {ι : Type} [Fintype ι] (κ : ℝ) (Y : F.Cell) (j : ι → ↥(chordBonds (finiteCells F)))
    (ζ : BondField ι) : ℝ :=
  ∑ i, Real.exp (-(2 ^ 5 * κ * bondDistToCell Y (j i))) * ‖ζ i‖ ^ 2
def SmoothIncrementsOnTwoToriAt (P : StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F F' : BlockFrame) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (Y : F.Cell) (Y' : F'.Cell) (q : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F'))) (ζ : BondField ι),
    IsAdmissibleAt P t x f F V → IsAdmissibleAt P t x f F' V' →
    IsRegularFamily P.L t P.n₀ P.σ P.decayRate P.E P.energyRatio f →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → IsShortPairing Y Y' q j j' → P.blockIndex ≤ q →
    (∀ i, ‖ζ i‖ < P.ballRadius) →
    |(coldHalfLawAt P x f).blockIncrement Y (toTorus j ζ) V -
        (coldHalfLawAt P x f).blockIncrement Y' (toTorus j' ζ) V'| ≤
      Real.exp (-(4 * P.κ * q)) * (C * weightedBondNorm P.κ Y j ζ) ∧
    |(coldHalfLawAt P x f).linearBlockPart Y (toTorus j ζ) V -
        (coldHalfLawAt P x f).linearBlockPart Y' (toTorus j' ζ) V'| ≤
      Real.exp (-(4 * P.κ * q)) *
        (C * weightedBondNorm P.κ Y j ζ + C * (x * weightedBondNormSq P.κ Y j ζ + 1)) ∧
    ∀ (i : Fin 4) (back : Bool),
      |(coldHalfLawAt P x f).scoreRemainderIncrement (cellBond Y i back) (toTorus j ζ) V -
        (coldHalfLawAt P x f).scoreRemainderIncrement (cellBond Y' i back) (toTorus j' ζ) V'| ≤
      Real.exp (-(4 * P.κ * q)) * (C * weightedBondNorm P.κ Y j ζ)
def WeightedIncrementsOnOneTorusAt (P : StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V V' : F.GaugeField F.top) (Y : F.Cell) (q : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (j j' : ι → ↥(chordBonds (finiteCells F))) (ζ : BondField ι)
    (w : F.Site F.depth → ℝ) (B : ℝ),
    IsAdmissibleAt P t x f F V → IsAdmissibleAt P t x f F V' →
    IsRegularFamily P.L t P.n₀ P.σ P.decayRate P.E P.energyRatio f →
    AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → IsShortPairing Y Y q j j' → P.blockIndex ≤ q →
    (∀ i, ‖ζ i‖ < P.ballRadius) → 0 < B → (∀ y, |w y| ≤ B) →
    |(coldHalfLawAt P x f).weightedShareIncrement w Y (toTorus j ζ) V -
        (coldHalfLawAt P x f).weightedShareIncrement w Y (toTorus j' ζ) V'| ≤
      Real.exp (-(4 * P.κ * q)) * (C * B * weightedBondNorm P.κ Y j ζ)
def SmoothIncrementsOnTwoTori : Prop :=
  ∃ C : StepParameters → ℝ, (∀ P, 0 ≤ C P) ∧ EventuallyInParameters fun P =>
    SmoothIncrementsOnTwoToriAt P (C (parametersBeforeSide P)) ∧
      WeightedIncrementsOnOneTorusAt P (C (parametersBeforeSide P))
end YangMills.Construction.WeightedResponses
end
