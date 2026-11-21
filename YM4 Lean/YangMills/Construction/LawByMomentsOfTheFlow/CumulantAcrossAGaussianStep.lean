import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
section GaussianStep
variable {Ω ι : Type} [Fintype ι]
def gaussianStepQuadratic (S : Matrix ι ι ℝ) (W : Ω → ℝ) (l : Ω → ι → ℝ) (c : ℝ) (x : Ω × EuclideanSpace ℝ ι) : ℝ :=
  W x.1 + c + ∑ b, l x.1 b * x.2 b + (1 / 2) * ∑ b, ∑ b', S b b' * x.2 b * x.2 b'
def gaussianStepGradient (S : Matrix ι ι ℝ) (l : Ω → ι → ℝ) (b : ι) (x : Ω × EuclideanSpace ℝ ι) : ℝ :=
  l x.1 b + ∑ b', S b b' * x.2 b'
end GaussianStep
def cumulantAcrossGaussianStepStatement : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
      (G : Matrix ι ι ℝ) (S : Fin k → Matrix ι ι ℝ) (W : Fin k → Ω → ℝ) (l : Fin k → Ω → ι → ℝ) (c : Fin k → ℝ)
      (w : Fin k → ι → ℝ) (A ε : ℝ),
      G.PosSemidef → (∀ i, (S i).IsSymm) → 1 ≤ A → (∀ i b, 0 < w i b) →
      (∀ i, Measurable (W i)) → (∀ i b, Measurable fun ξ => l i ξ b) →
      (∀ i, Integrable (fun ξ => |W i ξ| ^ k) ρ ∧ ∫ ξ, |W i ξ| ^ k ∂ρ ≤ A ^ k) →
      (∀ i, Integrable (fun x => |gaussianStepQuadratic (S i) (W i) (l i) (c i) x| ^ k) (ρ.prod (multivariateGaussian 0 G)) ∧
        ∫ x, |gaussianStepQuadratic (S i) (W i) (l i) (c i) x| ^ k ∂(ρ.prod (multivariateGaussian 0 G)) ≤ A ^ k) →
      (∀ i b, Integrable (fun x => |gaussianStepGradient (S i) (l i) b x| ^ k) (ρ.prod (multivariateGaussian 0 G)) ∧
        ∫ x, |gaussianStepGradient (S i) (l i) b x| ^ k ∂(ρ.prod (multivariateGaussian 0 G)) ≤ w i b ^ k) →
      (∀ i j, i ≠ j → ∑ b, ∑ b', w i b * |G b b'| * w j b' ≤ ε) →
      |jointCumulant (ρ.prod (multivariateGaussian 0 G)) (fun i => gaussianStepQuadratic (S i) (W i) (l i) (c i)) -
        jointCumulant ρ W| ≤ C * A ^ k * ε
end YangMills.Construction.MomentLaw
end
