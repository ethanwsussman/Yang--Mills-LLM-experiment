import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace YangMills.Construction.ResponseInTheExpansion
open StepGas TorusFields WeightedResponses
def siteScoreHasIntegrableMajorant : Prop :=
  HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n), G.IsAdmissibleGround →
    ∀ y : TorusSite (n * R.params.side),
    ∃ B : G.Config → ℝ≥0∞, Measurable B ∧
      (∀ σ, G.pairConstraint.IsAdmissible σ → ENNReal.ofReal (chartSiteScore A (configSetting G σ) y) ≤ B σ) ∧
      ∫⁻ σ, B σ * G.pairConstraint.weightDensity G.weight σ ∂Measure.pi (G.referenceMeasure ∅) ≠ ⊤
end YangMills.Construction.ResponseInTheExpansion
end
