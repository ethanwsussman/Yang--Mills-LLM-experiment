import YangMills.Construction.ResponseInTheExpansion.OneStepToSecondOrder
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ResponseInTheExpansion
variable {Ω : Type} [MeasurableSpace Ω]
def tailSum {q : ℕ} (M : ℕ) (ζ : ℕ → Fin q → Ω → ℝ) (top : Fin q → Ω → ℝ) (j : ℕ) (i : Fin q) (ω : Ω) : ℝ :=
  ∑ u ∈ Finset.Ico j M, ζ u i ω + top i ω
structure IsGaussianChain {q : ℕ} (μ : Measure Ω) (K X Y ε : ℝ) (M : ℕ) (A : ℕ → Set Ω) (Xs : ℕ → ℝ)
    (Γ Γc : ℕ → Fin q → Fin q → ℝ) (ζ : ℕ → Fin q → Ω → ℝ) (top : Fin q → Ω → ℝ) (s : ℕ → Ω → ℝ) : Prop where
  isProbability : IsProbabilityMeasure μ
  one_le_K : 1 ≤ K
  X_pos : 0 < X
  X_le_one : X ≤ 1
  one_le_Y : 1 ≤ Y
  ε_nonneg : 0 ≤ ε
  scale_nonneg : ∀ u < M, 0 ≤ Xs u
  scale_le : ∀ u < M, Xs u ≤ 2 * X
  scale_sq_near : ∀ u < M, |Xs u ^ 2 - X ^ 2| ≤ K * ((u : ℝ) + 1) * X ^ 4
  cov_le : ∀ u < M, ∀ i i', |Γ u i i'| ≤ K * (1 / 4 : ℝ) ^ u
  stepCov_near : ∀ u < M, ∀ i i', |Γc u i i' - Γ u i i'| ≤ ε
  event_measurable : ∀ j, MeasurableSet (A j)
  event_mono : ∀ j, A j ⊆ A (j + 1)
  measure_compl_le : μ.real (A 0)ᶜ ≤ ε
  var_aesm : ∀ u < M, ∀ i, AEStronglyMeasurable ((A u).indicator (ζ u i)) μ
  top_aesm : ∀ i, AEStronglyMeasurable ((A M).indicator (top i)) μ
  var_le : ∀ u < M, ∀ i, ∀ᵐ ω ∂μ, ω ∈ A u → |ζ u i ω| ≤ K * (1 / 2 : ℝ) ^ u
  top_le : ∀ i, ∀ᵐ ω ∂μ, ω ∈ A M → |top i ω| ≤ K * (1 / 2 : ℝ) ^ M
  size_aesm : ∀ j ≤ M, AEStronglyMeasurable ((A j).indicator (s j)) μ
  size_nonneg : ∀ j ω, 0 ≤ s j ω
  size_le : ∀ j ω, s j ω ≤ K
  size_moment : ∀ j ≤ M, ∫ ω, (A j).indicator (fun ω => s j ω ^ (2 * q + 2)) ω ∂μ ≤ (K * X * Y) ^ (2 * q + 2)
  small_depth : (1 / 2 : ℝ) ^ M ≤ X ^ (4 * q + 4)
  small_error : ε * ((M : ℝ) + 1) * 4 ^ M ≤ X ^ (4 * q + 4)
  step_moment : ∀ j < M, ∀ (r : ℕ), 1 ≤ r → r ≤ 2 * q + 2 → ∀ (f : Fin r → Fin q) (S : Finset (Fin q)),
    |∫ ω, (A j).indicator (fun ω => (∏ a, ζ j (f a) ω) * ∏ i ∈ S, tailSum M ζ top (j + 1) i ω) ω ∂μ -
        Xs j ^ r * wickPairingSum (fun a b => Γc j (f a) (f b)) *
          ∫ ω, (A (j + 1)).indicator (fun ω => ∏ i ∈ S, tailSum M ζ top (j + 1) i ω) ω ∂μ| ≤
      ∫ ω, (A (j + 1)).indicator (fun ω => |∏ i ∈ S, tailSum M ζ top (j + 1) i ω| *
          (K * (1 / 2 : ℝ) ^ j * (X ^ (r + 1) + X ^ r * s (j + 1) ω) + ε)) ω ∂μ
def gaussianMomentsAlongChainStatement : Prop :=
  ∀ (q : ℕ) (K : ℝ), ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (X Y ε : ℝ) (M : ℕ) (A : ℕ → Set Ω)
    (Xs : ℕ → ℝ) (Γ Γc : ℕ → Fin q → Fin q → ℝ) (ζ : ℕ → Fin q → Ω → ℝ) (top : Fin q → Ω → ℝ) (s : ℕ → Ω → ℝ),
    IsGaussianChain μ K X Y ε M A Xs Γ Γc ζ top s →
    (∀ i, AEStronglyMeasurable ((A 0).indicator (tailSum M ζ top 0 i)) μ) ∧
    (∀ᵐ ω ∂μ, ω ∈ A 0 → ∀ i, |tailSum M ζ top 0 i ω| ≤ C) ∧
    Integrable ((A 0).indicator fun ω => ∏ i, tailSum M ζ top 0 i ω) μ ∧
    (∀ i i', |∑ u ∈ Finset.range M, Γ u i i'| ≤ C) ∧
    |∫ ω, (A 0).indicator (fun ω => ∏ i, tailSum M ζ top 0 i ω) ω ∂μ -
        X ^ q * wickPairingSum (fun i i' => ∑ u ∈ Finset.range M, Γ u i i')| ≤ C * X ^ (q + 1) * Y
end ResponseInTheExpansion
end YangMills.Construction
end
