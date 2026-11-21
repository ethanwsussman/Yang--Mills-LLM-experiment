import YangMills.Construction.ResponseInTheExpansion.ComparisonFromBoundsOfAMove
import YangMills.Construction.ResponseInTheExpansion.MeansOfTheSmoothMoves
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames Interpolation WeightedResponses
def smoothIncrementBoundsAt (P : StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell),
    IsAdmissibleAt P t x f F V →
    IsRegularFamily P.L t P.n₀ P.σ P.decayRate P.E P.energyRatio f →
    IsVanishingMoveWithGradient P.ballRadius x P.κ C 0 Y (fun η => (coldHalfLawAt P x f).blockIncrement Y η V) ∧
    IsVanishingMoveWithGradient P.ballRadius x P.κ C C Y (fun η => (coldHalfLawAt P x f).linearBlockPart Y η V) ∧
    (∀ (i : Fin 4) (back : Bool), IsVanishingMoveWithGradient P.ballRadius x P.κ C 0 Y
      (fun η => (coldHalfLawAt P x f).scoreRemainderIncrement (cellBond Y i back) η V)) ∧
    ∀ (w : F.Site F.depth → ℝ) (B : ℝ), 0 < B → (∀ z, |w z| ≤ B) →
      IsVanishingMoveWithGradient P.ballRadius x P.κ (C * B) 0 Y
        (fun η => (coldHalfLawAt P x f).weightedShareIncrement w Y η V)
def smoothIncrementBounds : Prop :=
  ∃ C : StepParameters → ℝ, (∀ P, 0 ≤ C P) ∧
    EventuallyInParameters fun P => smoothIncrementBoundsAt P (C (parametersBeforeSide P))
end ResponseInTheExpansion
end YangMills.Construction
end
