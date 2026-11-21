import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConvexPotentials
open ColdStepAtMirrorFrames
def cutoffIntegral {ι : Type} [Fintype ι] (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) : ℝ :=
  ∫ η, ballDensity (cutoffFactor ρ p) Ψ η
def FourCornerLogRatioBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ m κ : ℝ) (d : ι → ι → ℝ)
    (Ψ : Fin 2 → Fin 2 → BondField ι → ℝ) (K : Fin 2 → Fin 2 → ι → ι → ℝ) (p : ℝ → ℝ)
    (Bf Bg : ι → ℝ) (Bc M : ℝ),
    0 < ρ → 0 < m → 0 ≤ κ → IsCutoff ρ p → IsPseudoMetricOnBonds d →
    (∀ i j, IsUniformlyConvexDecaying ρ m κ d (Ψ i j) (K i j)) →
    (∀ i j, ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |Ψ i j η| ≤ M) →
    (∀ j, ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b,
      bondGradNorm (fun ζ => Ψ 1 j ζ - Ψ 0 j ζ) b η ≤ Bf b) →
    (∀ i, ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b,
      bondGradNorm (fun ζ => Ψ i 1 ζ - Ψ i 0 ζ) b η ≤ Bg b) →
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |Ψ 1 1 η + Ψ 0 0 η - Ψ 1 0 η - Ψ 0 1 η| ≤ Bc) →
    (∀ i j, 0 < cutoffIntegral ρ p (Ψ i j)) ∧
    |Real.log (cutoffIntegral ρ p (Ψ 1 1)) + Real.log (cutoffIntegral ρ p (Ψ 0 0)) -
        Real.log (cutoffIntegral ρ p (Ψ 1 0)) - Real.log (cutoffIntegral ρ p (Ψ 0 1))| ≤
      m⁻¹ * (∑ b, ∑ b', Bf b * Real.exp (-(κ * d b b')) * Bg b') + Bc
end YangMills.Construction.ConvexPotentials
end
