import YangMills.Construction.Torus.FunctionsOfSeveralPointsOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ProductNorms
open AmbientPoints
def cnNormOn {s : Conventions.StandingParameters} {E : ReflectionPositivity.AxisMirror.Ambient}
    {p : ℕ} (ν : ℕ) (A : Set (Tuple s E p)) (H : Tuple s E p → ℂ) : ℝ≥0∞ :=
  ⨆ α : YangMills.Construction.PowerSeries.MultiIndex (4 * p), ⨆ _ : α.order ≤ ν, ⨆ y ∈ A,
    ENNReal.ofReal ‖multiDeriv α H y‖
def ProductBoundsClaim : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : ReflectionPositivity.AxisMirror.Ambient) (p : ℕ)
    (hp : 1 ≤ p) (ν : ℕ),
    (∀ F H : Tuple s E p → ℂ, IsCn (ν : ℕ∞) F → IsCn (ν : ℕ∞) H →
      cnNorm ν F < ∞ → cnNorm ν H < ∞ →
      IsCn (ν : ℕ∞) (fun y => F y * H y) ∧
        cnNorm ν (fun y => F y * H y) ≤ 2 ^ ν * cnNorm ν F * cnNorm ν H) ∧
    (∀ (F H : Tuple s E p → ℂ) (A : Set (Tuple s E p)),
      IsCn (ν : ℕ∞) F → IsCn (ν : ℕ∞) H → cnNorm ν F < ∞ →
      A.Nonempty → SupportedIn F A →
      (∀ α : YangMills.Construction.PowerSeries.MultiIndex (4 * p), α.order ≤ ν →
        ∃ C : ℝ, ∀ y ∈ A, ‖multiDeriv α H y‖ ≤ C) →
      IsCn (ν : ℕ∞) (fun y => F y * H y) ∧
        cnNorm ν (fun y => F y * H y) ≤ 2 ^ ν * cnNorm ν F * cnNormOn ν A H) ∧
    (∀ (φ : Fin p → Pt s E → ℂ) (b : ℂ),
      (fun y => b * tensorProd φ y) =
        tensorProd (Function.update φ ⟨0, hp⟩ (fun x => b * φ ⟨0, hp⟩ x)))
end YangMills.Construction.ProductNorms
