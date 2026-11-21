import YangMills.Construction.ResponseInTheExpansion.MeanOfASlotOfOrderTwo
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open BlockAverages ColdStepAtMirrorFrames
variable {F : BlockFrame}
structure HasRemainderBounds (T : StepParameters) (x A : ℝ) (Y : F.Cell) (K : AboveFrames F) (V : F.GaugeField F.top) :
    Prop where
  smooth : ∀ (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    (∀ b, ‖η b‖ ≤ T.ballRadius) → ContDiffAt ℝ 2 (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      K q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η)
  deriv_le : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 → AreUnitVectors X →
    ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
      |bondDeriv (K η) V c X| ≤ A * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
        ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) *
          (‖η b‖ + x * ‖η b‖ ^ 3)
  gradNorm_le : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 1 →
    AreUnitVectors X →
    ∀ (η : StepVariable (finiteCells F)) (b₀ : ↥(chordBonds (finiteCells F))), (∀ b, ‖η b‖ < T.ballRadius) →
      bondGradNorm (fun ζ => bondDeriv (K ζ) V c X) b₀ η ≤ A * Real.exp (-(2 ^ 5 * T.κ * bondSpan Y c)) *
        Real.exp (-(2 * T.κ * (cellSupDist (enclosingCell b₀.1.1) Y : ℝ))) *
        (x * ∑ b : ↥(chordBonds (finiteCells F)), Real.exp (-(T.κ * (cellSupDist (enclosingCell b.1.1) Y : ℝ))) *
          ‖η b‖ ^ 2 + 1)
def RemainderOfBoundsAt (T : StepParameters) (A : ℝ) (Cq : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell) (K : AboveFrames F),
    IsAdmissibleAt T t x f F V → HasRemainderBounds T x A Y K V →
    IsSecondOrderRemainder T x f Cq C (C * x ^ (-(1 / 2) : ℝ)) Y K V
def remainderOfBoundsStatement : Prop :=
  ∀ A : StepParameters → ℝ, (∀ T, 0 ≤ A T) → ∃ (Cq : StepParameters → ℕ → ℝ) (C : StepParameters → ℝ),
    (∀ T q, 0 ≤ Cq T q) ∧ (∀ T, 0 < C T) ∧
    EventuallyInParameters fun T => RemainderOfBoundsAt T (A (parametersBeforeSide T)) (Cq (parametersBeforeSide T))
      (C (parametersBeforeSide T))
end YangMills.Construction.WeightedResponses
end
