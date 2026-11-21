import YangMills.Construction.ResponseInTheExpansion.ColdPartAtTheParameters
import YangMills.Construction.ResponseInTheExpansion.FramesMoveWithTheTop
import YangMills.Construction.ResponseInTheExpansion.TailOfAScore
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.WeightedResponses
namespace ResponseInTheExpansion
def ExpectationsEquivariantAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    ∀ (F : BlockFrame) (V : F.GaugeField F.top), IsCubicTopTorus T.L t T.n₀ F → IsSmallCurvature (5 / 4 * T.σ) V →
    (∀ (γ : F.Cell → UnitQuaternion) (Y : F.Cell),
      (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).linearBlockPart Y) (gaugeTransform γ V) =
        (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).linearBlockPart Y) V ∧
      (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockIncrement Y) (gaugeTransform γ V) =
        (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockIncrement Y) V) ∧
    (∀ (γ : F.Cell → UnitQuaternion) (c : F.Site F.top × Fin 4),
      (coldHalfLawAt T x f).scoreRemainderAt c 0 (gaugeTransform γ V) = (coldHalfLawAt T x f).scoreRemainderAt c 0 V ∧
      (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).scoreRemainderIncrement c) (gaugeTransform γ V) =
        (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).scoreRemainderIncrement c) V) ∧
    (∀ (h Y : F.Cell),
      (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).linearBlockPart (Y + h)) (translateField h V) =
        (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).linearBlockPart Y) V ∧
      (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockIncrement (Y + h)) (translateField h V) =
        (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockIncrement Y) V) ∧
    ∀ (h : F.Cell) (c : F.Site F.top × Fin 4),
      (coldHalfLawAt T x f).scoreRemainderAt (c.1 + h, c.2) 0 (translateField h V) =
        (coldHalfLawAt T x f).scoreRemainderAt c 0 V ∧
      (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).scoreRemainderIncrement (c.1 + h, c.2))
          (translateField h V) =
        (coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).scoreRemainderIncrement c) V
def expectationsEquivariantStatement : Prop :=
  ∀ T : StepParameters, T.IsOrdered → 2 ^ 40 ≤ T.L → 64 ≤ T.n₀ → FramesEquivariantAt T →
    ExpectationsEquivariantAt T
end ResponseInTheExpansion
end YangMills.Construction
end
