import YangMills.Construction.ResponseInTheExpansion.BlockRemainderAboveTheFrame
import YangMills.Construction.ResponseInTheExpansion.ExponentIsLocal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames
def BlockRemainderNearValueAt (T : ColdStepAtMirrorFrames.StepParameters) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x e : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell)
    (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    WeightedResponses.IsAdmissibleAt T t x f F V →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → 0 < e →
    WeightedResponses.IsTorusRemainder T.L T.σ T.decayRate e (e / T.η₃) r → k ≤ 2 → AreUnitVectors X →
    |(WeightedResponses.coldHalfLawAt T x f).expectation V
          (fun η => bondDeriv ((WeightedResponses.coldHalfLawAt T x f).blockSum r Y η) V c X) -
        bondDeriv ((WeightedResponses.coldHalfLawAt T x f).blockSum r Y 0) V c X| ≤
      C * (e / T.η₃) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
def blockRemainderNearValueStatement : Prop :=
  ∃ C : ColdStepAtMirrorFrames.StepParameters → ℝ, (∀ T, 0 < C T) ∧
    EventuallyInParameters fun T => BlockRemainderNearValueAt T (C (WeightedResponses.parametersBeforeSide T))
end YangMills.Construction.ResponseInTheExpansion
end
