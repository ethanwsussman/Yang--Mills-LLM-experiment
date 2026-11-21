import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMembers
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.ResponseInTheExpansion.InverseOfACoordinateHessian
import YangMills.Construction.ResponseInTheExpansion.WickFromByParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
open ColdStepAtMirrorFrames
structure IsNearHessian {ι : Type} [Fintype ι] [DecidableEq ι] (ρ lam x κ Dc W K₀ Ci S : ℝ)
    (d kk : ι → ι → ℝ) (P : BondField ι → ℝ) (H : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) : Prop where
  isPseudoMetric : IsPseudoMetricOnBonds d
  convexMember : IsConvexClassMember ρ (x * lam / 4) κ d P
  weight_sum : ∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W
  deriv_bound : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ (b : ι) (e : BondVector),
    |bondPartialDeriv P b η e| ≤ Dc * x * ‖e‖
  isSymm : H.IsSymm
  isUnit_det : IsUnit H.det
  inverse_bound : ∀ l : ι × Fin 3 → ℝ, ∑ r, |H⁻¹.mulVec l r| ≤ Ci * ∑ r, |l r|
  deriv_near_linear : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ r : ι × Fin 3,
    |fderiv ℝ P η (bondCoordinateVector r) - x * H.mulVec (fun c => η c.1 c.2) r| ≤
      K₀ * (1 + x * (∑ b', kk r.1 b' * ‖η b'‖) ^ 2)
  kernel_nonneg : ∀ b b', 0 ≤ kk b b'
  kernel_sum : ∀ b, ∑ b', kk b b' ≤ S
def GaussianMomentsNearHessian : Prop :=
  ∀ (ρ : ℝ) (p : ℝ → ℝ) (lam Dc W K₀ Ci S : ℝ), 0 < ρ → IsCutoff ρ p → 0 < lam → 0 ≤ Dc → 0 ≤ W →
    0 ≤ K₀ → 0 ≤ Ci → 0 ≤ S → ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x κ : ℝ) (d kk : ι → ι → ℝ) (P : BondField ι → ℝ)
        (H : Matrix (ι × Fin 3) (ι × Fin 3) ℝ), 1 ≤ x → 0 ≤ κ →
        IsNearHessian ρ lam x κ Dc W K₀ Ci S d kk P H → ∀ l : Fin q → ι × Fin 3 → ℝ,
        |ballExpectation (cutoffFactor ρ p) P (fun η => ∏ i, ∑ r, l i r * η r.1 r.2) -
            x ^ (-(q : ℝ) / 2) * Wick.pairingSum (fun i j => l i ⬝ᵥ H⁻¹.mulVec (l j)) Finset.univ| ≤
          C * x ^ (-((q : ℝ) + 1) / 2) * ∏ i, ∑ r, |l i r|
end YangMills.Construction.LinearResponse
end
