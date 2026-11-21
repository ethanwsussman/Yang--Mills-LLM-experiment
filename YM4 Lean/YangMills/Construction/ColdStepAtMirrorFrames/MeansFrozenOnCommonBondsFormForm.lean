import YangMills.Construction.ColdStepAtMirrorFrames.MeanAlongASegmentForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {ι 𝒞 : Type} [Fintype ι]
def weightedSqNormAt (κ : ℝ) (pl : ι → 𝒞) (D : 𝒞 → 𝒞 → ℝ) (Z : 𝒞) (η : BondField ι) : ℝ :=
  ∑ b, Real.exp (-(2 ^ 6 * κ * D Z (pl b))) * ‖η b‖ ^ 2
structure IsDecayingPlacement [Fintype 𝒞] (κ S : ℝ) (pl : ι → 𝒞) (D : 𝒞 → 𝒞 → ℝ) : Prop where
  self : ∀ Z, D Z Z = 0
  symm : ∀ Z Z', D Z Z' = D Z' Z
  triangle : ∀ Z Z' Z'', D Z Z'' ≤ D Z Z' + D Z' Z''
  bonds : ∀ Z, ∑ b, Real.exp (-(κ / 2 * D Z (pl b))) ≤ S
  cells : ∀ Z, ∑ Z', Real.exp (-(κ / 2 * D Z Z')) ≤ S
def placementDist (pl : ι → 𝒞) (D : 𝒞 → 𝒞 → ℝ) (b b' : ι) : ℝ := D (pl b) (pl b')
structure IsLocalDecomposition [Fintype 𝒞] [DecidableEq ι] (ρ x κ A : ℝ) (pl : ι → 𝒞) (D : 𝒞 → 𝒞 → ℝ)
    (θ : 𝒞 → BondField ι → ℝ) (Ψ H : BondField ι → ℝ) (Y : 𝒞) : Prop where
  smooth : ∀ Z, ContDiff ℝ 2 (θ Z)
  smooth_obs : ContDiff ℝ 1 H
  sum : ∀ η ∈ openPolyball ι ρ, Ψ η = ∑ Z, θ Z η
  slope : ∀ Z, ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm (θ Z) b η ≤
    A * (x * Real.sqrt (weightedSqNormAt κ pl D Z η) + 1) * Real.exp (-(2 ^ 5 * κ * D Z (pl b)))
  second : ∀ Z, ∀ η ∈ openPolyball ι ρ, ∀ (b b' : ι) (u u' : BondVector),
    |secondDerivAlong (θ Z) η (bondVariation b u) (bondVariation b' u')| ≤
      A * x * Real.exp (-(2 ^ 5 * κ * max (D Z (pl b)) (D Z (pl b')))) * ‖u‖ * ‖u'‖
  slope_obs : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm H b η ≤
    A * (x * Real.sqrt (weightedSqNormAt κ pl D Y η) + 1) * Real.exp (-(2 ^ 5 * κ * D Y (pl b)))
variable {Λ ι' 𝒞' 𝒩 : Type} [Fintype Λ] [Fintype ι']
open Classical in
def zeroExtensionL [DecidableEq ι] (e : Λ → ι) : BondField Λ →L[ℝ] BondField ι :=
  ContinuousLinearMap.pi fun b =>
    if h : ∃ l, e l = b then ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Λ => BondVector) h.choose
    else 0
def IsConvexWithSmallGradient [DecidableEq ι] (ρ m κ : ℝ) (d : ι → ι → ℝ) (Ψ : BondField ι → ℝ) : Prop :=
  (∃ K, IsUniformlyConvexDecaying ρ m κ d Ψ K) ∧
    ∀ (b : ι) (v : BondVector), |bondPartialDeriv Ψ b 0 v| ≤ Real.sqrt m * ‖v‖
end YangMills.Construction.ColdStepAtMirrorFrames
end
