import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import YangMills.Construction.ResponseInTheExpansion.TiltsOfTheGas
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open StepGas WeightedResponses
def covarianceByTwoTiltsStatement : Prop :=
  HoldsAtEveryStep fun _ R _ => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround → ∀ f g w : G.Config → ℝ,
    Measurable g → Measurable w → (∀ σ, G.pairConstraint.IsAdmissible σ → 1 ≤ w σ ∧ |g σ| ≤ w σ) →
    Integrable f (G.gibbsLaw ∅) → Integrable w (G.gibbsLaw ∅) → Integrable (fun σ => f σ * w σ) (G.gibbsLaw ∅) →
    Integrable (fun σ => f σ * g σ) (G.gibbsLaw ∅) ∧ Integrable g (G.gibbsLaw ∅) ∧
    Integrable f (tiltedGibbsLaw G fun σ => 2 * w σ + g σ) ∧ Integrable f (tiltedGibbsLaw G fun σ => 2 * w σ) ∧
    |G.expectation ∅ (fun σ => f σ * g σ) - G.expectation ∅ f * G.expectation ∅ g| ≤
      3 * G.expectation ∅ w * (|∫ σ, f σ ∂(tiltedGibbsLaw G fun σ => 2 * w σ + g σ) - G.expectation ∅ f| +
        |∫ σ, f σ ∂(tiltedGibbsLaw G fun σ => 2 * w σ) - G.expectation ∅ f|)
end YangMills.Construction.ResponseInTheExpansion
end
