import YangMills.Construction.FormsOnATorus.MeansOfAFieldDownTheChain
import YangMills.Construction.ResponseInTheExpansion.CurvatureOnTheBareTorus
import YangMills.Construction.ResponseInTheExpansion.JointLawOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.BlockAverages
def FinalFieldLawIsChainExpectation : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side →
    ∀ (β : ℝ) (x : ℕ → ℝ) (s n : ℕ) [NeZero n] (F : TorusField n → ENNReal),
    Measurable F → (∀ V, F V ≤ 1) → Measurable (chainExpectation ℓ x s n F) ∧
      (∀ U, chainExpectation ℓ x s n F U ≤ 1) ∧
      ∫ u, (F (finalField ℓ s n u)).toReal ∂(chainJointLaw ℓ β x s n) =
        ∫ U, (chainExpectation ℓ x s n F U).toReal ∂(wilsonLaw β (fineSide ℓ.side s n))
end YangMills.Construction.WeightedResponses
end
