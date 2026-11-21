import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import YangMills.Construction.SummableBoundsOfTheFlow.MeansOfTheGapObservable
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames FamilyNorms MeasureTheory
open BlockAverages hiding bondSpread
namespace BlockMeans
def GapMeansDominatedAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (φ : LocalFamily) (F : BlockFrame) (Y : F.Cell) (V : F.GaugeField F.top) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    T.coupling ≤ x → IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio φ → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V →
    ∃ r K : ℝ, 0 < r ∧ IsDominatedSmoothFamily (volume.restrict (Set.Icc (0 : ℝ) 1)) 3 (Metric.ball 0 r) K
      (fun (τ : Fin k → ℝ) (s : ℝ) => gapObservableMean T x s φ Y (leftTranslate (bondSpread c X τ) V))
def gapMeansDominated : Prop := EventuallyInParameters GapMeansDominatedAt
end BlockMeans
end YangMills.Construction
end
