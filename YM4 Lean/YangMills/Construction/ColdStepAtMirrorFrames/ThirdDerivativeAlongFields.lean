import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace ThirdDerivative
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : Type}
structure IsCutoffMeasureData (ρ : ℝ) (r : ℝ → ℝ) (Ψ : BondField ι → ℝ) : Prop where
  pos : 0 < ρ
  radial : IsRadialCutoff ρ r
  smooth : ContDiff ℝ 3 Ψ
def InOpenBalls (ρ : ℝ) (η : BondField ι) : Prop := ∀ b, ‖η b‖ < ρ
def extendedCutoff (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : ℝ := cutoffFactor ρ p (max u 0)
structure IsSiteDistance (δ : X → X → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ δ x y
  symm : ∀ x y, δ x y = δ y x
  triangle : ∀ x y z, δ x z ≤ δ x y + δ y z
def expWeight (δ : X → X → ℝ) (r : ℝ) (x y : X) : ℝ := Real.exp (-(r * δ x y))
def fieldAlong (z : ι → BondVector → BondVector) (η : BondField ι) : BondField ι :=
  fun b => z b (η b)
structure ThirdJetBound (ρ : ℝ) (G : BondField ι → ℝ) (E E₃ : ℝ) (wa : ι → ℝ) : Prop where
  smooth : ContDiff ℝ 3 G
  first : ∀ η, InOpenBalls ρ η → ∀ (b : ι) (e : BondVector),
    |fderiv ℝ G η (bondVariation b e)| ≤ E * wa b * ‖e‖
  second : ∀ η, InOpenBalls ρ η → ∀ (b b' : ι) (e e' : BondVector),
    |fderiv ℝ (fderiv ℝ G) η (bondVariation b e) (bondVariation b' e')| ≤ E * wa b * wa b' * (‖e‖ * ‖e'‖)
  third : ∀ η, InOpenBalls ρ η → ∀ (b b' b'' : ι) (e e' e'' : BondVector),
    |fderiv ℝ (fderiv ℝ (fderiv ℝ G)) η (bondVariation b e) (bondVariation b' e') (bondVariation b'' e'')| ≤
      E₃ * wa b * wa b' * wa b'' * (‖e‖ * ‖e'‖ * ‖e''‖)
structure FieldC1Bound (ρ : ℝ) (z : ι → BondVector → BondVector) (u : ι → ℝ) : Prop where
  smooth : ∀ b, ContDiff ℝ 1 (z b)
  norm_le : ∀ b (v : BondVector), ‖v‖ < ρ → ‖z b v‖ ≤ u b
  deriv_le : ∀ b (v : BondVector), ‖v‖ < ρ → ‖fderiv ℝ (z b) v‖ ≤ u b
def secondDerivAlong (G : BondField ι → ℝ) (z w : ι → BondVector → BondVector) (η : BondField ι) : ℝ :=
  fderiv ℝ (fderiv ℝ G) η (fieldAlong z η) (fieldAlong w η)
def derivAlong (G : BondField ι → ℝ) (z : ι → BondVector → BondVector) (η : BondField ι) : ℝ :=
  fderiv ℝ G η (fieldAlong z η)
structure FieldC2Bound (ρ : ℝ) (z : ι → BondVector → BondVector) (u : ι → ℝ) : Prop where
  smooth : ∀ b, ContDiff ℝ 2 (z b)
  norm_le : ∀ b (v : BondVector), ‖v‖ < ρ → ‖z b v‖ ≤ u b
  deriv_le : ∀ b (v : BondVector), ‖v‖ < ρ → ‖fderiv ℝ (z b) v‖ ≤ u b
  second_deriv_le : ∀ b (v : BondVector), ‖v‖ < ρ → ‖fderiv ℝ (fderiv ℝ (z b)) v‖ ≤ u b
def thirdDerivAlong (G : BondField ι → ℝ) (z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ : ι → BondVector → BondVector)
    (η : BondField ι) : ℝ :=
  fderiv ℝ (fderiv ℝ (fderiv ℝ G)) η (fieldAlong z₁ η) (fieldAlong z₂ η) (fieldAlong z₃ η) +
    secondDerivAlong G z₁₂ z₃ η + secondDerivAlong G z₁₃ z₂ η + secondDerivAlong G z₂₃ z₁ η +
      derivAlong G z₁₂₃ η
structure ConvexMeasureHyp (ρ : ℝ) (p : ℝ → ℝ) (m κ : ℝ) (d : ι → ι → ℝ)
    (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (c₁ W : ℝ) : Prop where
  pos : 0 < ρ
  cutoff : IsCutoff ρ p
  one_le : 1 ≤ m
  rate_pos : 0 < κ
  dist : IsPseudoMetricOnBonds d
  convex : IsUniformlyConvexDecaying ρ m κ d Ψ K
  data : IsCutoffMeasureData ρ (extendedCutoff ρ p) Ψ
  slope_zero : ∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt m * ‖e‖
  standingConstraints : ∀ b, ∑ b', K b b' * Real.exp (κ * d b b') ≤ c₁ * m
  weight_sum : ∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W
  c₁_nonneg : 0 ≤ c₁
structure LocalizedMeasureHyp (ρ : ℝ) (p : ℝ → ℝ) (m κ : ℝ) (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ)
    (c₁ W a : ℝ) (δ : X → X → ℝ) (loc : ι → X) : Prop where
  measure : ConvexMeasureHyp ρ p m κ (fun b b' => δ (loc b) (loc b')) Ψ K c₁ W
  site_dist : IsSiteDistance δ
  weight_sum : ∀ z, ∑ b, expWeight δ (κ / 16) (loc b) z ≤ W
  rate_le : 4 * κ ≤ a
structure ThirdFieldBounds (ρ : ℝ) (δ : X → X → ℝ) (loc : ι → X) (a Dz : ℝ) (c1 c2 c3 : X)
    (z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ : ι → BondVector → BondVector) : Prop where
  one_le : 1 ≤ Dz
  first : FieldC2Bound ρ z₁ (fun b => Dz * expWeight δ a (loc b) c1)
  second : FieldC2Bound ρ z₂ (fun b => Dz * expWeight δ a (loc b) c2)
  third : FieldC2Bound ρ z₃ (fun b => Dz * expWeight δ a (loc b) c3)
  first_second : FieldC1Bound ρ z₁₂ (fun b => Dz * (expWeight δ a (loc b) c1 * expWeight δ a (loc b) c2))
  first_third : FieldC1Bound ρ z₁₃ (fun b => Dz * (expWeight δ a (loc b) c1 * expWeight δ a (loc b) c3))
  second_third : FieldC1Bound ρ z₂₃ (fun b => Dz * (expWeight δ a (loc b) c2 * expWeight δ a (loc b) c3))
  all_three : FieldC1Bound ρ z₁₂₃
    (fun b => Dz * (expWeight δ a (loc b) c1 * expWeight δ a (loc b) c2 * expWeight δ a (loc b) c3))
def CovarianceThirdDerivBound (ρ : ℝ) (p : ℝ → ℝ) (c₁ W Dz Cf : ℝ) : Prop :=
  ∀ (ι X : Type) [Fintype ι] [DecidableEq ι] (m κ a : ℝ) (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ)
    (δ : X → X → ℝ) (loc : ι → X) (g G : BondField ι → ℝ) (E E₃ : ℝ) (Y Y' c1 c2 c3 : X)
    (z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ : ι → BondVector → BondVector),
    LocalizedMeasureHyp ρ p m κ Ψ K c₁ W a δ loc → 0 ≤ E → E ≤ E₃ →
    ThirdJetBound ρ g E E₃ (fun b => expWeight δ a Y (loc b)) →
    ThirdJetBound ρ G E E₃ (fun b => expWeight δ a Y' (loc b)) →
    ThirdFieldBounds ρ δ loc a Dz c1 c2 c3 z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃ →
    |ballCovariance (extendedCutoff ρ p) Ψ g (thirdDerivAlong G z₁ z₂ z₃ z₁₂ z₁₃ z₂₃ z₁₂₃)| ≤
      Cf * (E * E₃ / Real.sqrt m) * expWeight δ (κ / 8) Y Y' *
        (expWeight δ (κ / 16) Y' c1 * expWeight δ (κ / 16) Y' c2 * expWeight δ (κ / 16) Y' c3)
end ThirdDerivative
def CovarianceThirdDerivBounded : Prop :=
  ∀ (ρ : ℝ) (p : ℝ → ℝ) (c₁ W Dz : ℝ), 0 < ρ → IsCutoff ρ p → 0 ≤ c₁ → 0 ≤ W → 1 ≤ Dz →
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ThirdDerivative.CovarianceThirdDerivBound ρ p c₁ W Dz Cf
end YangMills.Construction.ColdStepAtMirrorFrames
end
