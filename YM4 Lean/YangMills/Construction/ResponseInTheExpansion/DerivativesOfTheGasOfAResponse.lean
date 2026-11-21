import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusFields StepSettings RenormalizationStepParameters StepGas BlockAverages
variable {R : StepSetup}
def ResponseSetup.GasTermsSmooth (A : ResponseSetup R) (C : ℝ) : Prop :=
  ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ (V : TorusField n) (k : ℕ) (c : Fin k → TorusBond n)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ),
    IsCold (9 / 8 * R.params.threshold) (perturb c X τ V) →
    (∀ (y : TorusSite (n * R.params.side)) (h : PlaquetteWeight (fineSide R.params.side R.depth (n * R.params.side))),
      ContDiffAt ℝ 40 (fun τ' => gasResponseShift A (coldCaseGround R (perturb c X τ' V)) y h) τ ∧
      (k ≤ 3 → AreUnitVectors X →
        ‖iteratedFDeriv ℝ 40 (fun τ' => gasResponseShift A (coldCaseGround R (perturb c X τ' V)) y h) τ‖ ≤
          R.coupling ^ C * weightNorm R.params.side R.depth h)) ∧
    ∀ b : TorusBond n,
      ContDiffAt ℝ 40 (fun τ' => gasBondScoreShift (coldCaseGround R (perturb c X τ' V)) b) τ ∧
      (k ≤ 3 → AreUnitVectors X →
        ‖iteratedFDeriv ℝ 40 (fun τ' => gasBondScoreShift (coldCaseGround R (perturb c X τ' V)) b) τ‖ ≤
          R.coupling ^ C)
def GasTermsOfResponseSmooth : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧ ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∀ K : ResponseParameters, ∃ C y₀ : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ (R : StepSetup) (A : ResponseSetup R),
      A.responseParams = K → OnStepParameters T y A → R.IsSymmetricWeight → A.GasTermsSmooth C
end YangMills.Construction.WeightedResponses
end
