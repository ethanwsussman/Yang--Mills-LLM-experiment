import YangMills.Construction.ResponseInTheExpansion.BlockRemainderAboveTheFrame
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace WeightedResponses
def blockSumExpectationNearValueAt (T : StepParameters) : Prop :=
  ∃ C : ℝ, ∀ (t : ℕ) (x e : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (r : F.Site F.depth → F.GaugeField F.depth → ℝ) (Y : F.Cell)
    (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsAdmissibleAt T t x f F V →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → 0 < e →
    IsTorusRemainder T.L T.σ T.decayRate e (e / T.η₃) r → 1 ≤ k → k ≤ 2 → AreUnitVectors X →
    |bondDeriv ((coldHalfLawAt T x f).expectationOf ((coldHalfLawAt T x f).blockSum r Y)) V c X -
        bondDeriv ((coldHalfLawAt T x f).blockSum r Y 0) V c X| ≤
      C * (e / T.η₃) * x ^ (-(1 / 2) : ℝ) * Real.exp (-(T.κ / 2 ^ 6 * bondSpan Y c))
def blockSumExpectationNearValueStatement : Prop :=
  EventuallyInParameters blockSumExpectationNearValueAt
end WeightedResponses
end YangMills.Construction
end
