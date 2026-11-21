import YangMills.Construction.ColdStepAtMirrorFrames.MeanAlongASegmentForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def radialSlopeIntegral (S : Finset ι) (F : BondField ι → ℝ) (x : BondField ι) : ℝ :=
  ∑ b ∈ S, ∫ t in (0 : ℝ)..1, bondPartialDeriv F b (t • x) (x b)
def RadialSlopeIntegralBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Finset ι) (ρ B₀ A : ℝ) (F : BondField ι → ℝ),
    0 < ρ → ContDiffOn ℝ 2 F (openPolyball ι ρ) →
    (∀ b ∈ S, ∀ e, |bondPartialDeriv F b 0 e| ≤ B₀ * ‖e‖) →
    (∀ x ∈ openPolyball ι ρ, ∀ b ∈ S, ∀ c e e',
      |secondDerivAlong F x (bondVariation b e) (bondVariation c e')| ≤ A * ‖e‖ * ‖e'‖) →
    ∀ x ∈ openPolyball ι ρ,
      DifferentiableAt ℝ (radialSlopeIntegral S F) x ∧
      |radialSlopeIntegral S F x| ≤ ∑ b ∈ S, ‖x b‖ * (B₀ + A * ∑ c, ‖x c‖) ∧
      ∀ c, bondGradNorm (radialSlopeIntegral S F) c x ≤
        (if c ∈ S then B₀ + A * ∑ c', ‖x c'‖ else 0) + A * ∑ b ∈ S, ‖x b‖
end YangMills.Construction.ColdStepAtMirrorFrames
end
