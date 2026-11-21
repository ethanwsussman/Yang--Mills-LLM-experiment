import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.ParametricMinima
def HessianSplitsAtPartialMinimum : Prop :=
  ∀ (A B : Type) [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (E : A × B → ℝ) (s : B → A) (P : B →L[ℝ] A),
    ContDiffAt ℝ 2 E (0, 0) → s 0 = 0 → (∀ᶠ b in 𝓝 (0 : B), DifferentiableAt ℝ s b) →
    HasFDerivAt s P 0 →
    (∀ᶠ b in 𝓝 (0 : B), ∀ e : A, fderiv ℝ E (s b, b) (e, 0) = 0) →
    ∀ (x : A) (y : B),
      fderiv ℝ (fderiv ℝ E) (0, 0) (x, y) (x, y) =
        fderiv ℝ (fderiv ℝ fun b => E (s b, b)) 0 y y +
          fderiv ℝ (fderiv ℝ E) (0, 0) (x - P y, 0) (x - P y, 0)
end YangMills.Construction.ParametricMinima
end
