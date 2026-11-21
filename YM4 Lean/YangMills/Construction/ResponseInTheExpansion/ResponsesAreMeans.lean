import YangMills.Construction.ResponseInTheExpansion.ResponsesOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepCosts
def ResponseConditionalMeanStatement : Prop :=
  ∀ (params : StepParameters), params.Admissible → ∀ (β : ℝ) (x al : ℕ → ℝ),
    (∀ (t n : ℕ) [NeZero n] (Y : TorusSite n) (w : PlaquetteWeight (fineSide params.side t n)),
      Measurable (fun U : TorusField n => coldResponseChain params β x al t n Y U w) ∧
      ∃ C : ℝ, ∀ U, |coldResponseChain params β x al t n Y U w| ≤ C) ∧
    ∀ (t n : ℕ) [NeZero n] (w : PlaquetteWeight (fineSide params.side (t + 1) n)) (V : TorusField n),
      (∑ Y : TorusSite n, coldResponseChain params β x al (t + 1) n Y V w) * chainFunctional params β x (t + 1) n V =
        ∫ U : TorusField (n * params.side), chainFunctional params β x t (n * params.side) U *
          ∑ b : BaseChoice params.side n, stepTransitionDensity params (x t) U b V *
          (∑ z : TorusSite (n * params.side), coldResponseChain params β x al t (n * params.side) z U w +
            ∑ c : TorusBond n, params.coupling * al t * bondBlockMean params.side (t + 1) n w c *
              bondScore params (x t) U V b c)
          ∂(fieldHaar (n * params.side))
end YangMills.Construction.ResponseInTheExpansion
end
