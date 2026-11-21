import YangMills.Construction.Torus.MultilinearFormsOnCompactlySupportedComponents
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints
def BoundedMultilinearFormIsDistribution : Prop :=
  ∀ (s : Conventions.StandingParameters) (n : ℕ) (ρ c : ℝ) (O : Fin n → Set (Pt s .euclidean)),
    IsOpenTupleInBall ρ O → 0 ≤ c →
    ∀ B : EntryTuple O → ℝ, IsMultilinearOnComponents B → IsGradNormBounded c B →
      (∀ F : testFns (boxSet O),
        (∀ χ, IsCutoff O χ → CutOffIsOneOnProjections F.1 χ → IsCutoffFor χ F) ∧
        (∃ χ, IsCutoff O χ ∧ CutOffIsOneOnProjections F.1 χ) ∧
        ∀ χ, IsCutoffFor χ F →
          ∃ Fs : ℕ+ → Tuple s .euclidean n → ℂ,
            (∀ t, IsFiniteTensorSumWithin O χ (Fs t)) ∧
              TestFnTendsto (boxSet O) Fs F.1) ∧
      (∃! T, IsDistribExtending B T) ∧
      ∀ T, IsDistribExtending B T →
        (∀ (F : testFns (boxSet O)) (χ), IsCutoffFor χ F →
          ENNReal.ofReal ‖T F‖ ≤
            ENNReal.ofReal (2 ^ n * c * bumpNumber n ρ) *
              (∏ i, c1GradNorm fun x => (χ i x : ℂ)) * cnNorm (5 * n + 1) F.1) ∧
        HasOrderLE (5 * n + 1) T
end YangMills.Construction.AmbientPoints
