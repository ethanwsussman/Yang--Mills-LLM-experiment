import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.LocalTermsOfAMeasureForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory ColdStepAtMirrorFrames
namespace Freezing
def freezeGradientConstant (lam S : ℝ) : ℝ :=
  8 * S ^ 3 / lam * (Real.sqrt (64 * S ^ 2 / lam + 2) + S * Real.sqrt (32 * S / lam)) +
    4 * S ^ 2 * Real.sqrt (32 * S / lam)
structure HasFrozenGradientBound {ι P : Type} [Fintype ι] [DecidableEq ι] (ρ r A : ℝ) (p : ℝ → ℝ)
    (pos : ι → P) (D : P → P → ℝ) (Y : P) (T H : BondField ι → ℝ) : Prop where
  smooth : ContDiffOn ℝ 1 H (openPolyball ι ρ)
  sq_integrable : Integrable fun η => H η ^ 2 * ballDensity (cutoffFactor ρ p) T η
  grad_sq_integrable : ∀ b, Integrable fun η => bondGradNorm H b η ^ 2 * ballDensity (cutoffFactor ρ p) T η
  grad_norm_le : ∀ b, ballL2Norm (cutoffFactor ρ p) T (bondGradNorm H b) ≤ A * Real.exp (-(2 * r * D (pos b) Y))
def frozenExpectationDifferenceBound : Prop :=
  ∀ (ι P : Type) [Fintype ι] [DecidableEq ι] [Fintype P] (ρ r S lam x c R A B : ℝ) (p : ℝ → ℝ)
    (pos : ι → P) (D : P → P → ℝ) (Ψ H : BondField ι → ℝ) (θ : P → BondField ι → ℝ) (Y : P)
    (Λ : Finset ι), 0 < ρ → 0 < r → 0 < lam → 1 ≤ x → 1 ≤ c → 0 ≤ R → 0 ≤ A → IsCutoff ρ p →
    IsPseudoMetricOnBonds D → IsAdmissiblePotential ρ (x * lam / 4) r (fun b b' => D (pos b) (pos b')) Ψ →
    (∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S) →
    (∀ z, ∑ z', Real.exp (-(r / 4 * D z' z)) ≤ S) →
    (∀ z, IsLocalTermAt ρ r c x pos D z (θ z)) → (∀ η ∈ openPolyball ι ρ, Ψ η = ∑ z, θ z η) →
    (∀ b, b ∈ Λ ↔ D (pos b) Y ≤ R / 2) →
    Integrable (fun η => H η * radialWeightProd (cutoffFactor ρ p) η) →
    Integrable (fun η => H (restrictToBonds Λ η) * radialWeightProd (cutoffFactor ρ p) η) →
    (∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      HasFrozenGradientBound ρ r A p pos D Y (segmentInterpolant (frozenPotential Λ (x * lam) Ψ) Ψ v) H ∧
      HasFrozenGradientBound ρ r A p pos D Y (segmentInterpolant (frozenPotential Λ (x * lam) Ψ) Ψ v)
        (fun η => H (restrictToBonds Λ η)) ∧
      |ballExpectation (cutoffFactor ρ p) (segmentInterpolant (frozenPotential Λ (x * lam) Ψ) Ψ v)
        (fun η => H η - H (restrictToBonds Λ η))| ≤ B) →
    |ballExpectation (cutoffFactor ρ p) Ψ H -
      ballExpectation (cutoffFactor ρ p) (frozenPotential Λ (x * lam) Ψ) (fun η => H (restrictToBonds Λ η))| ≤
      B + A * (Real.sqrt x)⁻¹ * c * freezeGradientConstant lam S * Real.exp (-(r * R / 16))
end Freezing
end YangMills.Construction
end
