import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import YangMills.Construction.ResponseInTheExpansion.KernelsAboveTheFrames
import YangMills.Construction.ResponseInTheExpansion.MeansOfTheSmoothMoves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation WeightedResponses
namespace WeightedResponses
variable {F : BlockFrame}
namespace ColdHalfLaw
variable (Q : ColdHalfLaw)
open Classical in
def weightedSiteShares (w : F.Site F.depth → ℝ) (Y : F.Cell) : AboveFrames F := fun η V =>
  ∑ y ∈ (sitesOfCells (finiteCells F) F.depth).filter (fun y => enclosingCell y = Y),
    w y * minimalSiteShare Q.a y (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V η)
open Classical in
def blockGapTerms (Y : F.Cell) : AboveFrames F := fun η V =>
  (∑ c ∈ (innerBonds (finiteCells F) F.top).filter (fun c => c.1 = Y),
      haarGapExcess Q.a Q.coupling (interpolatedField 1 Q.a Q.chartRadius Q.mirrorRadius V η) c) +
    ∑ b : ↥(chordBonds (finiteCells F)), if enclosingCell b.1.1 = Y then
      haarLogRatio (interpolatedCoords 1 Q.a Q.chartRadius Q.mirrorRadius V η b.1.1 b.1.2) else 0
end ColdHalfLaw
end WeightedResponses
namespace ResponseInTheExpansion
def CostKernelBoundsAt (T : StepParameters) (B : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell), IsAdmissibleAt T t x f F V →
    HasDecayingKernels T.ballRadius B (2 ^ 7 * T.κ) Y ((coldHalfLawAt T x f).blockCost Y) V ∧
    (∀ (i : Fin 4) (back : Bool),
      HasDecayingKernels T.ballRadius B (2 ^ 7 * T.κ) Y ((coldHalfLawAt T x f).scoreRemainderAt (cellBond Y i back)) V) ∧
    (∀ (w : F.Site F.depth → ℝ) (B' : ℝ), 0 < B' → (∀ y, |w y| ≤ B') →
      HasDecayingKernels T.ballRadius (B * B') (2 ^ 7 * T.κ) Y ((coldHalfLawAt T x f).weightedSiteShares w Y) V) ∧
    HasDecayingKernels T.ballRadius B (2 ^ 7 * T.κ) Y ((coldHalfLawAt T x f).blockGapTerms Y) V ∧
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
      |bondDeriv ((coldHalfLawAt T x f).blockGapTerms Y 0) V c X| ≤ B * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c))
def costKernelBoundsStatement : Prop :=
  ∃ B : StepParameters → ℝ, (∀ T, 0 < B T) ∧
    EventuallyInParameters fun T => CostKernelBoundsAt T (B (parametersBeforeSide T))
end ResponseInTheExpansion
end YangMills.Construction
end
