import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
def QuadraticExpansionOfDensity : Prop :=
  ∀ z : ℝ, 0 < z → ∃ C : ℝ, ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ ξ : Tower.FullSpace.PositiveEdge (Tower.meshAt L 0 0) → ℝ, HasBoundedAngles ξ →
      ∀ f : ℝ, 4 * |f| ≤ min (Real.pi / 2) (z / 48) →
        DensityDefined z (fun e => f * ξ e) ∧ Summable (secondDerivativeTerm z ξ) ∧
          ‖densityAt z (fun e => f * ξ e) (0 : Tower.FullSpace.Vertex L 0 0) -
              densityAt z (fun _ => 0) (0 : Tower.FullSpace.Vertex L 0 0) -
              ((1 / 2 * f ^ 2 : ℝ) : ℂ) * secondDerivativeSum z ξ‖ ≤ C * |f| ^ 3
end YangMills.Construction.Tower.AbelianFieldDensity
end
