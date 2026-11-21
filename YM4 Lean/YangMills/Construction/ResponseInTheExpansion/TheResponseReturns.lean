import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import YangMills.Construction.ResponseInTheExpansion.ImageOfAResponse
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace WeightedResponses
open YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.ClusterExpansionOfAStep
def ReturnsAtParameters (T : ParameterAssignment) (K : ResponseParameters) (Cs y : ℝ) : Prop :=
  ∀ (R : StepSetup) (A : ResponseSetup R) (hL : CoarseLabelFacts R), A.responseParams = K →
    OnStepParameters T y A → R.IsSymmetricWeight →
    R.nextCoupling = R.shiftedCoupling T.lam → StepIsScored T.lam R A hL ∧
      ∃ c' : ℝ, |c' - A.coeff| ≤ Cs * R.coupling ^ (-(3 / 2) : ℝ) ∧ StepHasResponseBounds R A hL c' ∧
        ∀ c'' : ℝ, StepHasResponseBounds R A hL c'' → c'' = c'
def responseReturnsStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : ChainParameters → ℝ), (∀ c, 0 < rt₀ c) ∧
    ∀ T : ParameterAssignment, T.coupling = a → L₀ ≤ T.side → T.Admissible → T.ColdStepHolds →
      T.HoldsFrom ColdRegimeEstimatesAt →
      T.rt ≤ rt₀ T.toChainParameters → ∀ M : ℝ, ∃ K : ResponseParameters, M ≤ K.Kc ∧ K.η₃ = T.η₃ ∧
      K.N₀ = T.N 0 ∧ (∀ y : ℝ, K.Admissible (T.stepParameters y)) ∧
      ∃ Cs y₀ : ℝ, 0 ≤ Cs ∧ ∀ y : ℝ, y₀ ≤ y → ReturnsAtParameters T K Cs y
end WeightedResponses
end YangMills.Construction
end
