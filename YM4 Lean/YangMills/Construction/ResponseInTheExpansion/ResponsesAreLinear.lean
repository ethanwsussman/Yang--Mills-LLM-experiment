import YangMills.Construction.ResponseInTheExpansion.ResponsesOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
def ResponseLinearLocalStatement : Prop :=
  ∀ (params : StepParameters), params.Admissible → ∀ (β : ℝ) (x al : ℕ → ℝ) (t n : ℕ) [NeZero n] (Y : TorusSite n),
    (∀ (r r' : ℝ) (w w' : PlaquetteWeight (fineSide params.side t n)) (U : TorusField n),
      coldResponseChain params β x al t n Y U (fun p => r * w p + r' * w' p) =
        r * coldResponseChain params β x al t n Y U w + r' * coldResponseChain params β x al t n Y U w') ∧
    (∀ w w' : PlaquetteWeight (fineSide params.side t n), (∀ p, IsPlaquetteAt params.side t Y p → w p = w' p) →
      ∀ U, coldResponseChain params β x al t n Y U w = coldResponseChain params β x al t n Y U w') ∧
    ∀ (w : PlaquetteWeight (fineSide params.side (t + 1) n)) (V : TorusField n),
      responseRemainder (coldResponseChain params β x al (t + 1)) n Y w V =
        conditionalMean params (x t) (chainFunctional params β x t) V fun U _ =>
          ∑ z ∈ sitesInBlocks params.side {Y}, coldResponseChain params β x al t (n * params.side) z U
            (fun p => w p - blockMean params.side (t + 1) n Y w)
end YangMills.Construction.ResponseInTheExpansion
end
