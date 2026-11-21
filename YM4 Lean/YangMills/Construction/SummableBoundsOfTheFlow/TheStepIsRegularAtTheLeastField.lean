import YangMills.Construction.SummableBoundsOfTheFlow.LogAlongATilt
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames FamilyNorms
def IsRegularAtMinimizer (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (φ h : LocalFamily) (ε : ℝ), T.coupling ≤ x → 0 < ε →
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate T.E (T.E / T.η₃) (φ + θ • h)) →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate ε (ε / T.η₃) h →
    ∀ (F : BlockFrame), IsCubicTopTorus T.L t T.n₀ F → ∀ V : F.GaugeField F.top,
      IsSmallCurvature (9 / 8 * T.σ) V →
      (∀ b ∈ chordBonds (finiteCells F),
        ‖stepFrame true T.a T.chainParams.ρA 0 b V‖ + T.ballRadius < Real.pi) ∧
      (∃ w, IsMinimizingChart T.a (finiteCells F) V T.chainParams.ρA w) ∧
      (∃ M : ℝ, ∀ m₁ : ℕ, (¬ ∀ i, 4 * m₁ + 5 < F.extent i) →
        IsRegularStep T.a T.chainParams.ρA T.ballRadius T.chainParams.lam x M m₁ T.p φ V) ∧
      ∃ M : ℝ, IsRegularSegment T.a T.chainParams.ρA T.ballRadius x M (frameRadius x) T.p φ h V
def regularStepAtMinimizerStatement : Prop := EventuallyInParameters IsRegularAtMinimizer
end YangMills.Construction.Interpolation
end
