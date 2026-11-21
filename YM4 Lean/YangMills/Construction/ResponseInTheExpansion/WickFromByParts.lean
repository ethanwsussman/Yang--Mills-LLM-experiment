import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace Wick
open Classical in
def pairingSum {q : ℕ} (G : Fin q → Fin q → ℝ) (s : Finset (Fin q)) : ℝ :=
  ∑ π : Finpartition s,
    if ∀ B ∈ π.parts, B.card = 2 then
      ∏ B ∈ π.parts, (if h : B.Nonempty then G (B.min' h) (B.max' h) else 1)
    else 0
structure GaussianByParts {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {q : ℕ} (ξ R : Fin q → Ω → ℝ)
    (G : Fin q → Fin q → ℝ) (y : ℝ) (Λ : Fin q → ℝ) (A : ℕ → ℝ) (B : ℝ) : Prop where
  integrable_pow_field : ∀ i r, Integrable (fun ω => ξ i ω ^ (2 * r)) μ
  integrable_pow_remainder : ∀ i r, Integrable (fun ω => R i ω ^ (2 * r)) μ
  moment_field_le : ∀ i r, ∫ ω, ξ i ω ^ (2 * r) ∂μ ≤ A r * (Λ i * y) ^ (2 * r)
  moment_remainder_le : ∀ i r, ∫ ω, R i ω ^ (2 * r) ∂μ ≤ A r * Λ i ^ (2 * r)
  abs_covariance_le : ∀ i j, |G i j| ≤ B * Λ i * Λ j
  integration_by_parts : ∀ (s : Finset (Fin q)) (a : Fin q), a ∉ s → (∀ i ∈ s, i < a) →
    ∫ ω, (∏ i ∈ s, ξ i ω) * ξ a ω ∂μ =
      y ^ 2 * (∑ i ∈ s, G i a * ∫ ω, ∏ j ∈ s.erase i, ξ j ω ∂μ) -
        y ^ 2 * ∫ ω, (∏ i ∈ s, ξ i ω) * R a ω ∂μ
def WickOfIntegrationByParts : Prop :=
  ∀ (A : ℕ → ℝ) (B : ℝ), ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (q : ℕ)
      (ξ R : Fin q → Ω → ℝ) (G : Fin q → Fin q → ℝ) (y : ℝ) (Λ : Fin q → ℝ),
      0 < y → (∀ i, 0 < Λ i) → GaussianByParts μ ξ R G y Λ A B →
      ∀ s : Finset (Fin q),
        |(∫ ω, ∏ i ∈ s, ξ i ω ∂μ) - y ^ s.card * pairingSum G s| ≤
          C s.card * y ^ (s.card + 1) * ∏ i ∈ s, Λ i
end Wick
end YangMills.Construction
end
