import YangMills.Construction.Towers.TheDensityOfAnAbelianField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
def scaledLinearAngle (L : ℕ) (f : ℝ) : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ :=
  fun e => f * FullSpace.linearAbelianAngle e
def QuadraticResponseToConstantField : Prop :=
  ∀ z : ℝ, 0 < z → ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ,
    ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
      MassiveStiffnessExists hL z ∧
        ∀ f : ℝ, |f| ≤ r →
          DensityDefined z (scaledLinearAngle L f) ∧
            ‖densityAt z (scaledLinearAngle L f) (0 : FullSpace.Vertex L 0 0) -
                densityAt z (fun _ => 0) (0 : FullSpace.Vertex L 0 0) -
                ((1 / 2 * massiveStiffness hL z * f ^ 2 : ℝ) : ℂ)‖ ≤ C * |f| ^ 3
end YangMills.Construction.Tower.AbelianFieldDensity
end
