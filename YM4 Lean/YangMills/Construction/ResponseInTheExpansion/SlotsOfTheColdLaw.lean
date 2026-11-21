import YangMills.Construction.ResponseInTheExpansion.LawOfTheColdHalf
import YangMills.Construction.SummableBoundsOfTheFlow.ThirdOrderWithTwoFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Interpolation TorusComparison
namespace WeightedResponses
variable {F : BlockFrame}
structure IsSmoothBoundedSlot (Q : ColdHalfLaw) (Cq : ℕ → ℝ) (r : ℕ) (h : ℝ) (Y : F.Cell)
    (K : AboveFrames F) (V : F.GaugeField F.top) : Prop where
  smooth : ∀ (η : StepVariable (finiteCells F)) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (X : Fin k → imaginaryQuaternions),
    (∀ b, ‖η b‖ ≤ Q.ballRadius) → ContDiffAt ℝ r (fun q : (Fin k → ℝ) × StepVariable (finiteCells F) =>
      K q.2 (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X q.1) V)) (0, η)
  deriv_bound : ∀ (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    k < r → AreUnitVectors X →
    Q.HasSize Cq V (h * Real.exp (-(2 ^ 5 * Q.rate * bondSpan Y c))) Y fun η => bondDeriv (K η) V c X
def DecaysAlongTopField (Q : ColdHalfLaw) (Cq : ℕ → ℝ) (h : ℝ) (Y : F.Cell) (K : AboveFrames F)
    (V : F.GaugeField F.top) : Prop :=
  ∀ (Th : imaginaryQuaternions → imaginaryQuaternions → imaginaryQuaternions),
    (∀ w X : imaginaryQuaternions, ‖w‖ < Real.pi → IsRightTranslationDeriv w X (Th w X)) →
    ∀ (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (b : ↥(chordBonds (finiteCells F))), ‖X‖ = 1 →
      HasLocalSize Q.ballRadius Q.radialWeight (Q.exponent V) Cq Q.coupling Q.rate
        (Real.sqrt Q.coupling * h *
          Real.exp (-(2 ^ 4 * Q.rate * bondDistToCell Y b) - 2 ^ 6 * Q.rate * bondDistToTopBond b c))
        (bondDistToCell Y)
        (topFieldPartial Th 1 Q.a Q.chartRadius Q.mirrorRadius c X V b fun η => K η V)
structure IsSlot (Q : ColdHalfLaw) (Cq : ℕ → ℝ) (h : ℝ) (Y : F.Cell) (K : AboveFrames F)
    (V : F.GaugeField F.top) : Prop where
  smoothBounded : IsSmoothBoundedSlot Q Cq 3 h Y K V
  contDiffAt_two : ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < Q.ballRadius) →
    ContDiffAt ℝ 2 (fun ζ => K ζ V) η
  decaysAlongTopField : DecaysAlongTopField Q Cq h Y K V
end WeightedResponses
end YangMills.Construction
end
