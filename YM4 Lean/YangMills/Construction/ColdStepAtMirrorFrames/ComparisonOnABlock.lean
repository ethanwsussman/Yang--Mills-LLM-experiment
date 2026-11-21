import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.LocalTermsOfAMeasureForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def blockComparisonConstant (lam S : ℝ) : ℝ :=
  2 * ((4 / lam) * (64 * S ^ 2 / lam + 2)) * S ^ 3 + 32 * S ^ 2 / lam + 1
def BlockComparisonBound : Prop :=
  ∀ (ι ι' κ P P' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype κ]
    [DecidableEq κ] [Fintype P] [DecidableEq P] [Fintype P'] [DecidableEq P']
    (ρ r S lam x c ε R : ℝ) (p : ℝ → ℝ)
    (pos : ι → P) (D : P → P → ℝ) (Ψ H : BondField ι → ℝ) (θ : P → BondField ι → ℝ) (Y : P)
    (pos' : ι' → P') (D' : P' → P' → ℝ) (Ψ' H' : BondField ι' → ℝ)
    (θ' : P' → BondField ι' → ℝ) (Y' : P') (j : κ → ι) (j' : κ → ι')
    (M : Finset P) (M' : Finset P') (φ : {z // z ∈ M} ≃ {z // z ∈ M'}),
    0 < ρ → 0 < r → 0 < lam → 1 ≤ x → 1 ≤ c → 0 ≤ ε → 0 ≤ R → IsCutoff ρ p →
    IsPseudoMetricOnBonds D → IsPseudoMetricOnBonds D' →
    IsAdmissiblePotential ρ (x * lam / 4) r (fun b b' => D (pos b) (pos b')) Ψ →
    IsAdmissiblePotential ρ (x * lam / 4) r (fun b b' => D' (pos' b) (pos' b')) Ψ' →
    (∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S) →
    (∀ z, ∑ z', Real.exp (-(r / 4 * D z' z)) ≤ S) →
    (∀ z, ∑ b, Real.exp (-(r / 4 * D' (pos' b) z)) ≤ S) →
    (∀ z, ∑ z', Real.exp (-(r / 4 * D' z' z)) ≤ S) →
    (∀ z, IsLocalTermAt ρ r c x pos D z (θ z)) → (∀ η ∈ openPolyball ι ρ, Ψ η = ∑ z, θ z η) →
    (∀ z, IsLocalTermAt ρ r c x pos' D' z (θ' z)) → (∀ η ∈ openPolyball ι' ρ, Ψ' η = ∑ z, θ' z η) →
    IsLocalTermAt ρ r c x pos D Y H → IsLocalTermAt ρ r c x pos' D' Y' H' →
    Function.Injective j → Function.Injective j' →
    (∀ k k', D (pos (j k)) (pos (j k')) = D' (pos' (j' k)) (pos' (j' k'))) →
    (∀ k, D (pos (j k)) Y = D' (pos' (j' k)) Y') →
    (∀ z, z ∉ M → R / 8 ≤ D z Y) → (∀ z, z ∉ M' → R / 8 ≤ D' z Y') →
    (∀ (z : {z // z ∈ M}), ∀ ξ ∈ openPolyball κ ρ, ∀ k,
      bondGradNorm (fun ζ => θ' (φ z).1 (pushforwardField j' ζ) - θ z.1 (pushforwardField j ζ)) k ξ ≤
        c * ε * (x * Real.sqrt (weightedSqNormNear r (fun k => pos (j k)) D z.1 ξ) + 1) *
          Real.exp (-(2 * r * D (pos (j k)) z.1))) →
    (∀ ξ ∈ openPolyball κ ρ, |H' (pushforwardField j' ξ) - H (pushforwardField j ξ)| ≤
      c * ε * (x * weightedSqNormNear r (fun k => pos (j k)) D Y ξ + 1)) →
    |ballExpectation (cutoffFactor ρ p) (fun ξ => Ψ' (pushforwardField j' ξ))
        (fun ξ => H' (pushforwardField j' ξ)) -
      ballExpectation (cutoffFactor ρ p) (fun ξ => Ψ (pushforwardField j ξ))
        (fun ξ => H (pushforwardField j ξ))| ≤
      c ^ 2 * blockComparisonConstant lam S * (ε + Real.exp (-(r * R / 32)))
end YangMills.Construction.ColdStepAtMirrorFrames
end
