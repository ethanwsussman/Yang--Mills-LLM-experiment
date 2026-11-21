import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.LocalTermsOfAMeasureForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def freezingConstant (lam S : ℝ) : ℝ :=
  (16 * S ^ 2 / lam + 32 * S / lam + 1) * S +
    2 * S ^ 3 * ((4 / lam) * (64 * S ^ 2 / lam + 2) +
      S * ((4 / lam) * (64 * S ^ 2 / lam + 2) + 128 * S / lam ^ 2)) +
    lam * S ^ 2 * ((4 / lam) * (64 * S ^ 2 / lam + 2) + 128 * S / lam ^ 2)
def FreezingBoundOnTorus : Prop :=
  ∀ (ι P : Type) [Fintype ι] [DecidableEq ι] [Fintype P] (ρ r S lam x c R : ℝ) (p : ℝ → ℝ)
    (pos : ι → P) (D : P → P → ℝ) (Ψ H : BondField ι → ℝ) (θ : P → BondField ι → ℝ) (Y : P)
    (Λ : Finset ι), 0 < ρ → 0 < r → 0 < lam → 1 ≤ x → 1 ≤ c → 0 ≤ R → IsCutoff ρ p →
    IsPseudoMetricOnBonds D →
    IsAdmissiblePotential ρ (x * lam / 4) r (fun b b' => D (pos b) (pos b')) Ψ →
    (∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S) →
    (∀ z, ∑ z', Real.exp (-(r / 4 * D z' z)) ≤ S) →
    (∀ z, IsLocalTermAt ρ r c x pos D z (θ z)) → (∀ η ∈ openPolyball ι ρ, Ψ η = ∑ z, θ z η) →
    IsLocalTermAt ρ r c x pos D Y H → (∀ b, b ∈ Λ ↔ D (pos b) Y ≤ R / 2) →
    |ballExpectation (cutoffFactor ρ p) Ψ H -
      ballExpectation (cutoffFactor ρ p) (frozenPotential Λ (x * lam) Ψ)
        (fun η => H (restrictToBonds Λ η))| ≤
      c ^ 2 * freezingConstant lam S * Real.exp (-(r * R / 16))
end YangMills.Construction.ColdStepAtMirrorFrames
end
