import YangMills.Construction.ResponseInTheExpansion.BlockRemainderAboveTheFrame
import YangMills.Construction.ResponseInTheExpansion.SlotsOfTheColdLaw
import YangMills.Construction.ResponseInTheExpansion.SmoothMovesAreAdmitted
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames TorusComparison WeightedResponses
variable {F : BlockFrame}
def remainderIsSlotAt (T : ColdStepAtMirrorFrames.StepParameters) (Cq : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x e : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell),
    IsAdmissibleAt T t x f F V → IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → 0 < e →
    IsTorusRemainder T.L T.σ T.decayRate e (e / T.η₃) r →
    IsSlot (coldHalfLawAt T x f) Cq (C * (e / T.η₃) * x ^ (-(1 / 2) : ℝ)) Y
      ((coldHalfLawAt T x f).blockSum r Y) V
def remainderIsComparableAt (T : ColdStepAtMirrorFrames.StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x e : ℝ) (f : LocalFamily) (F : BlockFrame) (V V' : F.GaugeField F.top)
    (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell)
    (q : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (j j' : ι → ↥(chordBonds (finiteCells F))),
    IsAdmissibleAt T t x f F V → IsAdmissibleAt T t x f F V' →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → 0 < e →
    IsTorusRemainder T.L T.σ T.decayRate e (e / T.η₃) r →
    AgreeOnBall (finiteCells F) V (finiteCells F) V' Y Y q → IsShortPairing Y Y q j j' →
    IsComparablePair T x f (C * (e / T.η₃)) q Y Y j j' ((coldHalfLawAt T x f).blockSum r Y)
      ((coldHalfLawAt T x f).blockSum r Y) V V'
def remaindersAreSlotsStatement : Prop :=
  ∃ (Cq : ColdStepAtMirrorFrames.StepParameters → ℕ → ℝ) (C : ColdStepAtMirrorFrames.StepParameters → ℝ),
    (∀ T q, 0 ≤ Cq T q) ∧ (∀ T, 0 ≤ C T) ∧
    EventuallyInParameters fun T => remainderIsSlotAt T (Cq (sizeParameters T)) (C (parametersBeforeSide T)) ∧
      remainderIsComparableAt T (C (parametersBeforeSide T))
end YangMills.Construction.ResponseInTheExpansion
end
