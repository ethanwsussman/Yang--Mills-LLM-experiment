import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.MeansFrozenOnCommonBondsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {ι 𝒞 : Type} [Fintype ι]
variable {Λ ι' 𝒞' 𝒩 : Type} [Fintype Λ] [Fintype ι']
structure IsCloseInValue [DecidableEq ι] [DecidableEq ι'] [DecidableEq Λ] (ρ x κ ε : ℝ)
    (pl : ι → 𝒞) (D : 𝒞 → 𝒞 → ℝ) (e : Λ → ι) (e' : Λ → ι') (n : 𝒩 → 𝒞) (n' : 𝒩 → 𝒞')
    (θ : 𝒞 → BondField ι → ℝ) (θ' : 𝒞' → BondField ι' → ℝ)
    (H : BondField ι → ℝ) (H' : BondField ι' → ℝ) (Y : 𝒞) : Prop where
  terms : ∀ j, ∀ ζ ∈ openPolyball Λ ρ, |θ (n j) (zeroExtensionL e ζ) - θ' (n' j) (zeroExtensionL e' ζ)| ≤
    ε * (x * weightedSqNormAt κ pl D (n j) (zeroExtensionL e ζ) + 1)
  value : ∀ ζ ∈ openPolyball Λ ρ, |H (zeroExtensionL e ζ) - H' (zeroExtensionL e' ζ)| ≤
    ε * (x * weightedSqNormAt κ pl D Y (zeroExtensionL e ζ) + 1)
def ExpectationsAgreeInValue : Prop :=
  ∀ S lam : ℝ, 0 < lam → ∃ C : ℝ, (∀ (ι 𝒞 : Type) [Fintype ι] [DecidableEq ι] [Fintype 𝒞]
    [DecidableEq 𝒞] (ρ x κ A : ℝ) (p : ℝ → ℝ) (pl : ι → 𝒞) (D : 𝒞 → 𝒞 → ℝ)
    (Ψ H : BondField ι → ℝ) (Y : 𝒞), 0 < ρ → IsCutoff ρ p → 0 < κ → 1 ≤ x → 0 ≤ A →
    IsDecayingPlacement κ S pl D → IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) Ψ →
    Continuous H →
    (∀ η ∈ openPolyball ι ρ, |H η| ≤ A * (x * weightedSqNormAt κ pl D Y η + 1)) →
    |ballExpectation (cutoffFactor ρ p) Ψ H| ≤ C * A) ∧
  ∀ (ι ι' 𝒞 𝒞' Λ 𝒩 : Type) [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] [Fintype 𝒞] [DecidableEq 𝒞] [Fintype 𝒞'] [DecidableEq 𝒞']
    [Fintype Λ] [DecidableEq Λ] [Fintype 𝒩] [DecidableEq 𝒩]
    (ρ x κ A ε rad : ℝ) (p : ℝ → ℝ) (pl : ι → 𝒞) (D : 𝒞 → 𝒞 → ℝ) (pl' : ι' → 𝒞')
    (D' : 𝒞' → 𝒞' → ℝ) (e : Λ → ι) (e' : Λ → ι') (n : 𝒩 → 𝒞) (n' : 𝒩 → 𝒞')
    (θ : 𝒞 → BondField ι → ℝ) (θ' : 𝒞' → BondField ι' → ℝ)
    (Ψ H : BondField ι → ℝ) (Ψ' H' : BondField ι' → ℝ) (Y : 𝒞) (Y' : 𝒞'),
    0 < ρ → IsCutoff ρ p → 0 < κ → 1 ≤ x → 1 ≤ A → 0 < ε → 0 ≤ rad →
    IsDecayingPlacement κ S pl D → IsDecayingPlacement κ S pl' D' →
    Function.Injective e → Function.Injective e' → Function.Injective n → Function.Injective n' →
    (∀ l l', D (pl (e l)) (pl (e l')) = D' (pl' (e' l)) (pl' (e' l'))) →
    (∀ l, D Y (pl (e l)) = D' Y' (pl' (e' l))) →
    (∀ b, b ∉ Set.range e → rad / 2 ≤ D Y (pl b)) → (∀ b, b ∉ Set.range e' → rad / 2 ≤ D' Y' (pl' b)) →
    (∀ Z, Z ∉ Set.range n → rad / 8 ≤ D Y Z) → (∀ Z, Z ∉ Set.range n' → rad / 8 ≤ D' Y' Z) →
    IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl D) Ψ →
    IsConvexWithSmallGradient ρ (x * lam / 4) κ (placementDist pl' D') Ψ' →
    IsLocalDecomposition ρ x κ A pl D θ Ψ H Y → IsLocalDecomposition ρ x κ A pl' D' θ' Ψ' H' Y' →
    IsCloseInValue ρ x κ ε pl D e e' n n' θ θ' H H' Y →
    |ballExpectation (cutoffFactor ρ p) Ψ H - ballExpectation (cutoffFactor ρ p) Ψ' H'| ≤
      C * (A ^ 2 * Real.exp (-(κ * rad / 2 ^ 4)) + A * ε * (1 + Fintype.card 𝒩))
end YangMills.Construction.ColdStepAtMirrorFrames
end
