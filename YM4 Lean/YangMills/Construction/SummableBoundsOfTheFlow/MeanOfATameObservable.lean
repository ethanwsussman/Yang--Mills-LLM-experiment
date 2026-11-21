import YangMills.Construction.SummableBoundsOfTheFlow.TameObservablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ScaledVariables
def TiltedMeanDerivSmoothInScale : Prop :=
  ∀ (F : BlockFrame) (s ρ lo hi D a : ℝ) (w : ℝ → ℝ) (q : StepVariable (finiteCells F) → ℝ)
    (A Ob : ℝ → StepVariable (finiteCells F) → F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) (k : ℕ)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
    (∀ i, F.extent i ≠ 0) → 0 < ρ → 0 < lo → lo < a → a < hi → 0 ≤ D →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w → (∀ u, u < ρ → 0 < w u) → (∀ u, ρ ≤ u → w u = 0) → Continuous q →
    IsTameOnScales s ρ lo hi D A → IsTameOnScales s ρ lo hi D Ob → IsSmallCurvature s V →
    AreUnitVectors X → k ≤ 3 →
    ContDiffAt ℝ (if k = 3 then 2 else 3) (fun l => bondDeriv (tiltedMean w q A Ob l) V c X) a
end ScaledVariables
end YangMills.Construction
end
