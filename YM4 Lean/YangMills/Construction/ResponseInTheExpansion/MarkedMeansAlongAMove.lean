import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.ResponseInTheExpansion.CasesAtAColdTop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages TorusFields StepSettings RenormalizationStepParameters WeightedResponses
def FullyMarkedExpectationsSmooth (R : StepSetup) (C : ℝ) : Prop :=
  ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    ∀ (g : TorusField n → TorusField (n * R.params.side) → ℝ) (B : ℝ) (q : ℕ → ℝ), 0 ≤ B →
    (∀ V' W, |g V' W| ≤ B) → (∀ V', Measurable (g V')) →
    (∀ (k' : ℕ) (c' : Fin k' → TorusBond n) (X' : Fin k' → imaginaryQuaternions), AreUnitVectors X' →
      ∀ (V' : TorusField n) (W : TorusField (n * R.params.side)),
      ContDiff ℝ 40 (fun τ => g (perturb c' X' τ V') W) ∧
      ∀ τ, ∀ i, 1 ≤ i → i ≤ 40 → ‖iteratedFDeriv ℝ i (fun τ' => g (perturb c' X' τ' V') W) τ‖ ≤ q k') →
    (∀ k', k' ≤ 9 → q k' ≤ B) →
    ∀ (V : TorusField n) (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ),
      IsCold (9 / 8 * R.params.threshold) (perturb c X τ V) →
      ContDiffAt ℝ 40
        (fun τ' => fullyMarkedExpectation R (perturb c X τ' V) (g (perturb c X τ' V))) τ ∧
      (k ≤ 3 → AreUnitVectors X →
        ‖iteratedFDeriv ℝ 40
          (fun τ' => fullyMarkedExpectation R (perturb c X τ' V) (g (perturb c X τ' V))) τ‖ ≤
          R.coupling ^ C * B)
def FullyMarkedExpectationAlongPerturbation : Prop :=
  ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧
    ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters →
    ∃ C y₀ : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ R : StepSetup, R.OnParameters T y → R.IsSymmetricWeight →
      FullyMarkedExpectationsSmooth R C
end YangMills.Construction.ResponseInTheExpansion
end
