import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheGapObservable
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames FamilyNorms
namespace BlockMeans
def GapMeansDecayAt (P : StepParameters) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (t : ℕ) (x s : ℝ) (φ : LocalFamily) (F : BlockFrame) (Y : F.Cell)
    (V : F.GaugeField F.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    P.coupling ≤ x → 0 ≤ s → s ≤ 1 →
    IsNormBoundedLocalFamily P.L t P.n₀ P.σ P.decayRate P.E P.energyRatio φ →
    IsCubicTopTorus P.L t P.n₀ F → IsSmallCurvature (5 / 4 * P.σ) V → k ≤ 3 → AreUnitVectors X →
    |bondDeriv (gapObservableMean P x s φ Y) V c X| ≤
      C * (x ^ N)⁻¹ * Real.exp (-(P.chainParams.δ₂ / 4 * frameRadius x)) *
        Real.exp (-(P.κ / 2 ^ 6 * bondSpan Y c))
def gapMeansDecay : Prop := EventuallyInParameters GapMeansDecayAt
end BlockMeans
end YangMills.Construction
end
