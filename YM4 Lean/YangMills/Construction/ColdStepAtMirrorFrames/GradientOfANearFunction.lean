import YangMills.Construction.ColdStepAtMirrorFrames.MeanAlongASegmentForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def BondPartialDiffBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ₁ ρ₂ h M₀ M₂ : ℝ) (F₁ F₂ : BondField ι → ℝ),
    0 < h → 0 < ρ₁ → ρ₁ + h ≤ ρ₂ → ContDiffOn ℝ 2 F₁ (openPolyball ι ρ₂) → ContDiffOn ℝ 2 F₂ (openPolyball ι ρ₂) →
    (∀ x ∈ openPolyball ι ρ₂, |F₁ x - F₂ x| ≤ M₀) →
    (∀ x ∈ openPolyball ι ρ₂, ∀ (b : ι) (e : BondVector), ‖e‖ = 1 →
      |secondDerivAlong F₁ x (bondVariation b e) (bondVariation b e)| ≤ M₂) →
    (∀ x ∈ openPolyball ι ρ₂, ∀ (b : ι) (e : BondVector), ‖e‖ = 1 →
      |secondDerivAlong F₂ x (bondVariation b e) (bondVariation b e)| ≤ M₂) →
    ∀ x ∈ openPolyball ι ρ₁, ∀ (b : ι) (e : BondVector), ‖e‖ = 1 →
      |bondPartialDeriv F₁ b x e - bondPartialDeriv F₂ b x e| ≤ 2 * M₀ / h + 2 * M₂ * h
end YangMills.Construction.ColdStepAtMirrorFrames
end
