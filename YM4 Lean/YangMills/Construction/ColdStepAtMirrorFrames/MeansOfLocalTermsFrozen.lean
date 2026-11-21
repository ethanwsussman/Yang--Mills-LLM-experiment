import YangMills.Construction.ColdStepAtMirrorFrames.MeansFrozenOnCommonBondsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {ι 𝒞 : Type} [Fintype ι]
structure IsLocalDecompositionOnBalls [Fintype 𝒞] [DecidableEq ι] (ρ x κ A : ℝ) (pl : ι → 𝒞)
    (D : 𝒞 → 𝒞 → ℝ) (θ : 𝒞 → BondField ι → ℝ) (Ψ H : BondField ι → ℝ) (Y : 𝒞) : Prop where
  smooth : ∀ Z, ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 (θ Z) η
  smooth_obs : ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 H η
  sum : ∀ η ∈ openPolyball ι ρ, Ψ η = ∑ Z, θ Z η
  slope : ∀ Z, ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm (θ Z) b η ≤
    A * (x * Real.sqrt (weightedSqNormAt κ pl D Z η) + 1) * Real.exp (-(2 ^ 5 * κ * D Z (pl b)))
  second : ∀ Z, ∀ η ∈ openPolyball ι ρ, ∀ (b b' : ι) (u u' : BondVector), ‖u‖ = 1 → ‖u'‖ = 1 →
    |secondDerivAlong (θ Z) η (bondVariation b u) (bondVariation b' u')| ≤
      A * x * Real.exp (-(2 ^ 5 * κ * max (D Z (pl b)) (D Z (pl b'))))
  slope_obs : ∀ η ∈ openPolyball ι ρ, ∀ b, bondGradNorm H b η ≤
    A * (x * Real.sqrt (weightedSqNormAt κ pl D Y η) + 1) * Real.exp (-(2 ^ 5 * κ * D Y (pl b)))
end YangMills.Construction.ColdStepAtMirrorFrames
end
