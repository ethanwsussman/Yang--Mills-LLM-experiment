import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import YangMills.Construction.ResponseInTheExpansion.MeansOfTheSmoothMoves
import YangMills.Construction.ResponseInTheExpansion.SlotsOfTheColdLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open BlockAverages ColdStepAtMirrorFrames
variable {F : BlockFrame}
def IsSmoothSlotOfSize (P : StepParameters) (x : ℝ) (f : LocalFamily) (Cq : ℕ → ℝ) (C h : ℝ) (Y : F.Cell)
    (K : AboveFrames F) (V : F.GaugeField F.top) : Prop :=
  IsSlot (coldHalfLawAt P x f) Cq h Y K V ∧
    ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 →
      AreUnitVectors X →
      |(coldHalfLawAt P x f).expectation V (fun η => bondDeriv (K η) V c X)| ≤
        C * h * Real.exp (-(2 ^ 5 * P.κ * bondSpan Y c))
def SmoothIncrementsAreSlotsAt (P : StepParameters) (Cq : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell),
    IsAdmissibleAt P t x f F V → IsRegularFamily P.L t P.n₀ P.σ P.decayRate P.E P.energyRatio f →
    IsSmoothSlotOfSize P x f Cq C (C * x ^ (-(1 / 2) : ℝ)) Y ((coldHalfLawAt P x f).blockIncrement Y) V ∧
    IsSmoothSlotOfSize P x f Cq C C Y ((coldHalfLawAt P x f).linearBlockPart Y) V ∧
    (∀ (i : Fin 4) (back : Bool), IsSmoothSlotOfSize P x f Cq C (C * x ^ (-(1 / 2) : ℝ)) Y
      ((coldHalfLawAt P x f).scoreRemainderIncrement (cellBond Y i back)) V) ∧
    ∀ (w : F.Site F.depth → ℝ) (B : ℝ), 0 < B → (∀ y, |w y| ≤ B) →
      IsSmoothSlotOfSize P x f Cq C (C * B * x ^ (-(1 / 2) : ℝ)) Y
        ((coldHalfLawAt P x f).weightedShareIncrement w Y) V
def SmoothIncrementsAreSlots : Prop :=
  ∃ (Cq : StepParameters → ℕ → ℝ) (C : StepParameters → ℝ), (∀ P q, 0 ≤ Cq P q) ∧ (∀ P, 0 < C P) ∧
    EventuallyInParameters fun P =>
      SmoothIncrementsAreSlotsAt P (Cq (sizeParameters P)) (C (parametersBeforeSide P))
end YangMills.Construction.WeightedResponses
end
