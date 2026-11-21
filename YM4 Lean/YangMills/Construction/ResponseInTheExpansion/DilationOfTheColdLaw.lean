import YangMills.Construction.ResponseInTheExpansion.ColdPartAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation
namespace WeightedResponses
variable {F : BlockFrame}
namespace ColdHalfLaw
variable (Q : ColdHalfLaw)
def sumOverBlock (Y : F.Cell) (u : ↥(chordBonds (finiteCells F)) → ℝ) : ℝ :=
  open Classical in ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then u b else 0
def cutoffTerm (Y : F.Cell) : AboveFrames F := fun η _ =>
  sumOverBlock Y fun b => ‖η b‖ * deriv Q.cutoff ‖η b‖
def gapHaarExcess (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  (∑ c ∈ innerBonds (finiteCells F) F.top,
      haarGapExcess Q.a Q.coupling (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V η) c) +
    ∑ b : ↥(chordBonds (finiteCells F)),
      haarLogRatio (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η b.1.1 b.1.2)
def gapTerm (Y : F.Cell) : AboveFrames F := fun η V =>
  sumOverBlock Y fun b => bondPartialDeriv (fun ζ => Q.gapHaarExcess ζ V) b η (η b)
open Classical in
def familyTerm (Y : F.Cell) : AboveFrames F := fun η V =>
  ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
    ∑ b : ↥(chordBonds (finiteCells F)),
      bondPartialDeriv (fun ζ => interpolatedExpansion 1 Q.a Q.chartRadius Q.mirrorRadius Q.family y ζ V) b η (η b)
def slopeRemainder (b : ↥(chordBonds (finiteCells F))) (η : StepVariable (finiteCells F))
    (V : F.GaugeField F.top) : ℝ :=
  chartedSlope Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η) V b.1 (toImaginary (η b)) -
    2 * ∫ v in (0 : ℝ)..1,
      chartedSlope Q.a (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V (v • η)) V b.1 (toImaginary (η b))
def slopeTerm (Y : F.Cell) : AboveFrames F := fun η V =>
  Q.coupling * sumOverBlock Y fun b => Q.slopeRemainder b η V
def dilationRemainder (Y : F.Cell) (V : F.GaugeField F.top) : ℝ :=
  1 / (2 * Q.coupling) * Q.expectation V fun η =>
    - Q.cutoffTerm Y η V + Q.gapTerm Y η V + Q.familyTerm Y η V - Q.slopeTerm Y η V
end ColdHalfLaw
def dilationIdentityAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top), IsAdmissibleAt T t x f F V →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    x * (coldHalfLawAt T x f).expectation V
        (fun η => (coldHalfLawAt T x f).totalCost η V - (coldHalfLawAt T x f).totalCost 0 V) =
      3 / 2 * ((chordBonds (finiteCells F)).card : ℝ) +
        x * ∑ Y ∈ finiteCells F, (coldHalfLawAt T x f).dilationRemainder Y V
def dilationIdentity : Prop := EventuallyInParameters dilationIdentityAt
end WeightedResponses
end YangMills.Construction
end
