import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.BumpFunctions
def expNegInv (t : ℝ) : ℝ :=
  if 0 < t then Real.exp (-1 / t) else 0
def ExpNegInvIntegralBounds : Prop :=
  (Continuous expNegInv ∧
    (∀ t : ℝ, 0 ≤ expNegInv t ∧ expNegInv t ≤ 1) ∧
    (∀ t : ℝ, 0 < expNegInv t ↔ 0 < t)) ∧
  (Continuous (fun τ : ℝ => expNegInv τ * expNegInv (1 - τ)) ∧
    Continuous (fun t : ℝ => expNegInv (t + 1 / 4) * expNegInv (1 / 4 - t)) ∧
    (∀ τ : ℝ, expNegInv τ * expNegInv (1 - τ) ∈ Icc (0 : ℝ) 1) ∧
    (∀ t : ℝ, expNegInv (t + 1 / 4) * expNegInv (1 / 4 - t) ∈ Icc (0 : ℝ) 1) ∧
    (∀ τ ∈ Ioo (0 : ℝ) 1, 0 < expNegInv τ * expNegInv (1 - τ)) ∧
    (∀ τ : ℝ, τ ∉ Ioo (0 : ℝ) 1 → expNegInv τ * expNegInv (1 - τ) = 0) ∧
    (∀ t ∈ Ioo (-(1 / 4) : ℝ) (1 / 4),
      0 < expNegInv (t + 1 / 4) * expNegInv (1 / 4 - t)) ∧
    (∀ t : ℝ, t ∉ Ioo (-(1 / 4) : ℝ) (1 / 4) →
      expNegInv (t + 1 / 4) * expNegInv (1 / 4 - t) = 0)) ∧
  ((∀ t₁ : ℝ, 0 < t₁ → t₁ ≤ 1 →
      0 < ∫ τ in (0 : ℝ)..t₁, expNegInv τ * expNegInv (1 - τ) ∧
      ∫ τ in (0 : ℝ)..t₁, expNegInv τ * expNegInv (1 - τ) ≤ 1) ∧
    0 < ∫ t in (-(1 / 4) : ℝ)..(1 / 4), expNegInv (t + 1 / 4) * expNegInv (1 / 4 - t) ∧
    ∫ t in (-(1 / 4) : ℝ)..(1 / 4), expNegInv (t + 1 / 4) * expNegInv (1 / 4 - t) ≤ 1 / 2)
end YangMills.Construction.BumpFunctions
