import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
open ColdStepAtMirrorFrames
def PartialAlongBondFieldRegular : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {A : BondField ι → ℝ} {b : ι} {z : BondVector → BondVector} {B₁ Mz Mz' : ℝ}
    {B₂ : ι → ℝ}, (∀ ζ : BondField ι, (∀ b, ‖ζ b‖ < ρ) → ContDiffAt ℝ 3 A ζ) →
    (∀ v : BondVector, ‖v‖ < ρ → ContDiffAt ℝ 1 z v) →
    (∀ v : BondVector, ‖v‖ < ρ → ‖z v‖ ≤ Mz) → (∀ v : BondVector, ‖v‖ < ρ → ‖fderiv ℝ z v‖ ≤ Mz') →
    0 ≤ B₁ → (∀ b', 0 ≤ B₂ b') → 0 ≤ Mz → 0 ≤ Mz' →
    (∀ ζ : BondField ι, (∀ b, ‖ζ b‖ < ρ) → ∀ u : BondVector, |fderiv ℝ A ζ (Pi.single b u)| ≤ B₁ * ‖u‖) →
    (∀ ζ : BondField ι, (∀ b, ‖ζ b‖ < ρ) → ∀ (b' : ι) (u u' : BondVector),
      |fderiv ℝ (fderiv ℝ A) ζ (Pi.single b' u) (Pi.single b u')| ≤ B₂ b' * ‖u‖ * ‖u'‖) →
    ContDiffOn ℝ 1 (fun η : BondField ι => bondPartialDeriv A b η (z (η b))) {η | ∀ b, ‖η b‖ < ρ} ∧
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |bondPartialDeriv A b η (z (η b))| ≤ B₁ * Mz) ∧
    ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b' : ι,
      bondGradNorm (fun η : BondField ι => bondPartialDeriv A b η (z (η b))) b' η ≤
        B₂ b' * Mz + (if b' = b then B₁ * Mz' else 0)
end YangMills.Construction.LinearResponse
end
