import YangMills.Construction.ColdStepAtMirrorFrames.ComparisonOnABlock
import YangMills.Construction.ColdStepAtMirrorFrames.FreezingOnOneTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def BallExpectationFreezingBound : Prop :=
  ∀ (ι ι' P P' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype P]
    [DecidableEq P] [Fintype P'] [DecidableEq P']
    (ρ r S lam x c ε R : ℝ) (p : ℝ → ℝ)
    (pos : ι → P) (D : P → P → ℝ) (Ψ H : BondField ι → ℝ) (θ : P → BondField ι → ℝ) (Y : P)
    (pos' : ι' → P') (D' : P' → P' → ℝ) (Ψ' H' : BondField ι' → ℝ)
    (θ' : P' → BondField ι' → ℝ) (Y' : P') (Λ : Finset ι) (Λ' : Finset ι') (e : ↥Λ ≃ ↥Λ')
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
    (∀ b, b ∈ Λ ↔ D (pos b) Y ≤ R / 2) → (∀ b, b ∈ Λ' ↔ D' (pos' b) Y' ≤ R / 2) →
    (∀ k k' : ↥Λ, D (pos k.1) (pos k'.1) = D' (pos' (e k).1) (pos' (e k').1)) →
    (∀ k : ↥Λ, D (pos k.1) Y = D' (pos' (e k).1) Y') →
    (∀ z, z ∉ M → R / 8 ≤ D z Y) → (∀ z, z ∉ M' → R / 8 ≤ D' z Y') →
    (∀ (z : {z // z ∈ M}), ∀ ξ ∈ openPolyball ↥Λ ρ, ∀ k,
      bondGradNorm (fun ζ => θ' (φ z).1 (pushforwardField (fun k => (e k).1) ζ) -
        θ z.1 (pushforwardField (fun k : ↥Λ => k.1) ζ)) k ξ ≤
        c * ε * (x * Real.sqrt (weightedSqNormNear r (fun k : ↥Λ => pos k.1) D z.1 ξ) + 1) *
          Real.exp (-(2 * r * D (pos k.1) z.1))) →
    (∀ ξ ∈ openPolyball ↥Λ ρ,
      |H' (pushforwardField (fun k => (e k).1) ξ) - H (pushforwardField (fun k : ↥Λ => k.1) ξ)| ≤
        c * ε * (x * weightedSqNormNear r (fun k : ↥Λ => pos k.1) D Y ξ + 1)) →
    |ballExpectation (cutoffFactor ρ p) Ψ H - ballExpectation (cutoffFactor ρ p) Ψ' H'| ≤
      c ^ 2 * (2 * freezingConstant lam S * Real.exp (-(r * R / 16)) +
        blockComparisonConstant lam S * (ε + Real.exp (-(r * R / 32))))
end YangMills.Construction.ColdStepAtMirrorFrames
end
