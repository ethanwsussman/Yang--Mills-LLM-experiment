import YangMills.Construction.ResponseInTheExpansion.CasesAtAColdTop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages TorusFields TorusLumps StepCosts WeightedResponses
def KernelProductAlongPerturbation : Prop :=
  ∃ Cp : ℝ, 1 ≤ Cp ∧ ∀ (ℓ : StepParameters) (x : ℝ), ℓ.Admissible → 1 ≤ ℓ.coupling → 1 ≤ x →
    ∀ (n : ℕ) [NeZero n] (W : TorusField (n * ℓ.side)) (V : TorusField n)
    (b : BaseChoice ℓ.side n) (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) (S : ℝ),
    1 ≤ S → ∑ l, ‖X l‖ ≤ S →
    ContDiff ℝ 40 (fun τ => kernelProduct ℓ x W (perturb c X τ V) b) ∧
    (∀ τ, 0 < kernelProduct ℓ x W (perturb c X τ V) b) ∧
    (∀ τ, ∀ i ≤ 40, ‖iteratedFDeriv ℝ i (fun τ' => kernelProduct ℓ x W (perturb c X τ' V) b) τ‖ ≤
      (Cp * (ℓ.coupling * x) * ((k : ℝ) + 1) ^ 2 * S) ^ i * kernelProduct ℓ x W (perturb c X τ V) b) ∧
    (∀ τ τ', kernelProduct ℓ x W (perturb c X τ V) b ≤
      Real.exp (2 * (ℓ.coupling * x) * k) * kernelProduct ℓ x W (perturb c X τ' V) b) ∧
    ∀ c₀ : TorusBond n, ContDiff ℝ 40 (fun τ => bondScore ℓ x W (perturb c X τ V) b c₀) ∧
      ∀ τ, ∀ i, 1 ≤ i → i ≤ 40 →
        ‖iteratedFDeriv ℝ i (fun τ' => bondScore ℓ x W (perturb c X τ' V) b c₀) τ‖ ≤ (Cp * S) ^ i
end YangMills.Construction.ResponseInTheExpansion
end
