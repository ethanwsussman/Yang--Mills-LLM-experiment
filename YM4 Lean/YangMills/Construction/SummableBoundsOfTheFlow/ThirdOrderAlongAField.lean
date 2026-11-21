import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsWithTheirConstantsForm
import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongAField
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames BondIntegration Cumulants ConvexObservables Interpolation
namespace Estimates
structure IsBoundedC1BondField (v : BondVector → BondVector) : Prop where
  contDiff : ContDiff ℝ 1 v
  bounded : ∃ C, (∀ e, ‖v e‖ ≤ C) ∧ ∀ e, ‖fderiv ℝ v e‖ ≤ C
def CovarianceWithFieldDerivativeDecay : Prop :=
  ∀ (N : ℕ) (κ μ : ℝ), 0 < κ → 0 < μ →
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ (F : BlockFrame) (ι : Type) [Fintype ι] [DecidableEq ι] (y : ι → F.Cell) (ρ t : ℝ)
        (χ : ℝ → ℝ) (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ),
        0 < ρ → 0 < t → IsCutoff ρ χ →
        (∀ c, (Finset.univ.filter fun b => y b = c).card ≤ N) →
        IsUniformlyConvexDecaying ρ (t * μ / 4) κ (fun b b' => (cellSupDist (y b) (y b') : ℝ)) Ψ K →
        (∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt (t * μ / 4) * ‖e‖) →
        ∀ (A H R : BondField ι → ℝ) (v : ι → BondVector → BondVector) (Y Z : F.Cell)
          (CA CH CS : ℕ → ℝ) (a h h' s : ℝ) (w u : ι → ℝ),
          (∀ q, 0 ≤ CA q) → (∀ q, 0 ≤ CH q) → (∀ q, 0 ≤ CS q) → 0 ≤ a → 0 ≤ h → 0 ≤ h' → 0 ≤ s →
          (∀ b, 0 ≤ w b) → (∀ b, 0 ≤ u b) →
          ContDiffOn ℝ 1 A {η | ∀ b, ‖η b‖ < ρ} → ContDiffOn ℝ 1 H {η | ∀ b, ‖η b‖ < ρ} →
          ContDiffOn ℝ 1 R {η | ∀ b, ‖η b‖ < ρ} →
          (∀ b, ContDiffOn ℝ 1 (fieldDerivative b (v b) A) {η | ∀ b, ‖η b‖ < ρ}) →
          (∀ b, ContDiffOn ℝ 1 (fieldScore χ Ψ b (v b)) {η | ∀ b, ‖η b‖ < ρ}) →
          HasLocalSize ρ (cutoffFactor ρ χ) Ψ CA t κ a (fun b => (cellSupDist (y b) Y : ℝ)) A →
          (∀ b, HasLocalSize ρ (cutoffFactor ρ χ) Ψ CA t κ (a * w b) (fun b' => (cellSupDist (y b') Y : ℝ))
            (fieldDerivative b (v b) A)) →
          HasLocalSize ρ (cutoffFactor ρ χ) Ψ CH t κ h (fun b => (cellSupDist (y b) Z : ℝ)) H →
          HasLocalSize ρ (cutoffFactor ρ χ) Ψ CH t κ h' (fun b => (cellSupDist (y b) Z : ℝ)) R →
          (∀ b, HasLocalSize ρ (cutoffFactor ρ χ) Ψ CS t κ (s * u b) (fun b' => (cellSupDist (y b') (y b) : ℝ))
            (fieldScore χ Ψ b (v b))) →
          (∀ b, IsBoundedC1BondField (v b)) →
          Integrable (fun η => ((∑ b, fieldDerivative b (v b) H η) + R η) *
            ballDensity (cutoffFactor ρ χ) Ψ η) ∧
          Integrable (fun η => A η * ((∑ b, fieldDerivative b (v b) H η) + R η) *
            ballDensity (cutoffFactor ρ χ) Ψ η) ∧
          |ballCovariance (cutoffFactor ρ χ) Ψ A (fun η => (∑ b, fieldDerivative b (v b) H η) + R η)| ≤
            T * sizeConstantSum CA 3 * sizeConstantSum CH 3 *
              (sizeConstantSum CS 3 * a * h * s *
                  (∑ b, u b * Real.exp (-(κ / 8 * cellsDiameter ![Y, Z, y b]))) +
                a * h * (∑ b, w b) * Real.exp (-(κ / 8 * cellsDiameter ![Y, Z])) +
                a * h' * Real.exp (-(κ / 8 * cellsDiameter ![Y, Z])))
end Estimates
end YangMills.Construction
end
