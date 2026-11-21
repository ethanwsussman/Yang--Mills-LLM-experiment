import YangMills.Construction.SummableBoundsOfTheFlow.FreezingOfAFunction
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Freezing
def comparisonConstant (lam S : ℝ) : ℝ := 8 * S ^ 3 / lam * Real.sqrt (64 * S ^ 2 / lam + 2)
def expectationComparisonBound : Prop :=
  ∀ (ι ι' κ P P' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype κ]
    [DecidableEq κ] [Fintype P] [DecidableEq P] [Fintype P'] [DecidableEq P']
    (ρ r S lam x c ε R A B : ℝ) (p : ℝ → ℝ)
    (pos : ι → P) (D : P → P → ℝ) (Ψ : BondField ι → ℝ) (θ : P → BondField ι → ℝ) (Y : P)
    (pos' : ι' → P') (D' : P' → P' → ℝ) (Ψ' : BondField ι' → ℝ)
    (θ' : P' → BondField ι' → ℝ) (Y' : P') (j : κ → ι) (j' : κ → ι')
    (M : Finset P) (M' : Finset P') (φ : {z // z ∈ M} ≃ {z // z ∈ M'})
    (F F' : BondField κ → ℝ),
    0 < ρ → 0 < r → 0 < lam → 1 ≤ x → 1 ≤ c → 0 ≤ ε → 0 ≤ R → 0 ≤ A → IsCutoff ρ p →
    IsPseudoMetricOnBonds D → IsPseudoMetricOnBonds D' →
    IsAdmissiblePotential ρ (x * lam / 4) r (fun b b' => D (pos b) (pos b')) Ψ →
    IsAdmissiblePotential ρ (x * lam / 4) r (fun b b' => D' (pos' b) (pos' b')) Ψ' →
    (∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S) →
    (∀ z, ∑ z', Real.exp (-(r / 4 * D z' z)) ≤ S) →
    (∀ z, ∑ b, Real.exp (-(r / 4 * D' (pos' b) z)) ≤ S) →
    (∀ z, ∑ z', Real.exp (-(r / 4 * D' z' z)) ≤ S) →
    (∀ z, IsLocalTermAt ρ r c x pos D z (θ z)) → (∀ η ∈ openPolyball ι ρ, Ψ η = ∑ z, θ z η) →
    (∀ z, IsLocalTermAt ρ r c x pos' D' z (θ' z)) → (∀ η ∈ openPolyball ι' ρ, Ψ' η = ∑ z, θ' z η) →
    Function.Injective j → Function.Injective j' →
    (∀ k k', D (pos (j k)) (pos (j k')) = D' (pos' (j' k)) (pos' (j' k'))) →
    (∀ k, D (pos (j k)) Y = D' (pos' (j' k)) Y') →
    (∀ z, z ∉ M → R / 8 ≤ D z Y) → (∀ z, z ∉ M' → R / 8 ≤ D' z Y') →
    (∀ (z : {z // z ∈ M}), ∀ ξ ∈ openPolyball κ ρ, ∀ k,
      bondGradNorm (fun ζ => θ' (φ z).1 (pushforwardField j' ζ) - θ z.1 (pushforwardField j ζ)) k ξ ≤
        c * ε * (x * Real.sqrt (weightedSqNormNear r (fun k => pos (j k)) D z.1 ξ) + 1) *
          Real.exp (-(2 * r * D (pos (j k)) z.1))) →
    Integrable (fun ξ => F ξ * radialWeightProd (cutoffFactor ρ p) ξ) →
    Integrable (fun ξ => F' ξ * radialWeightProd (cutoffFactor ρ p) ξ) →
    (∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      HasFrozenGradientBound ρ r A p (fun k => pos (j k)) D Y
        (segmentInterpolant (fun ξ => Ψ (pushforwardField j ξ)) (fun ξ => Ψ' (pushforwardField j' ξ)) v) F ∧
      HasFrozenGradientBound ρ r A p (fun k => pos (j k)) D Y
        (segmentInterpolant (fun ξ => Ψ (pushforwardField j ξ)) (fun ξ => Ψ' (pushforwardField j' ξ)) v) F' ∧
      |ballExpectation (cutoffFactor ρ p)
        (segmentInterpolant (fun ξ => Ψ (pushforwardField j ξ)) (fun ξ => Ψ' (pushforwardField j' ξ)) v)
        (fun ξ => F' ξ - F ξ)| ≤ B) →
    |ballExpectation (cutoffFactor ρ p) (fun ξ => Ψ' (pushforwardField j' ξ)) F' -
      ballExpectation (cutoffFactor ρ p) (fun ξ => Ψ (pushforwardField j ξ)) F| ≤
      B + A * (Real.sqrt x)⁻¹ * c * comparisonConstant lam S * (ε + Real.exp (-(r * R / 32)))
end YangMills.Construction.Freezing
end
