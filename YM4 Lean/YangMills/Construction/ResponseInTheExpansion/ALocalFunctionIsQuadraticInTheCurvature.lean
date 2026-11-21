import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open Classical
open MeasureTheory
structure IsLocalGaugeFunctional {n : ℕ} [NeZero n] (σ K δ c ρ₀ : ℝ) (G : TorusField n → ℝ) (y : TorusSite n) : Prop where
  smooth : ∀ W, IsCold σ W → ContDiffThreeAt G W
  gauge_invariant : ∀ (g : TorusSite n → UnitQuaternion) (W : TorusField n), IsCold σ W → G (TorusFields.gaugeTransform g W) = G W
  decay : ∀ W, IsCold σ W → ∀ (k : ℕ) (b : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 3 → AreUnitVectors X →
    |mixedDeriv G W b X| ≤ K * Real.exp (-(δ * (supportDiam y b : ℝ)))
  agreement : ∀ W W', IsCold σ W → IsCold σ W' → FieldsAgreeNear W W' y y ⌊ρ₀⌋₊ →
    |G W - G W'| ≤ K * Real.exp (-(c * ρ₀))
  map_trivial : G (trivialField n) = 0
  deriv_trivial : ∀ (b : Fin 1 → TorusBond n) (X : Fin 1 → imaginaryQuaternions), mixedDeriv G (trivialField n) b X = 0
def kernelQuadraticForm {n : ℕ} [NeZero n] (κ : TorusPlaquette n → TorusPlaquette n → ℝ) (y : TorusSite n) (ρ₀ : ℝ)
    (F : TorusPlaquette n → imaginaryQuaternions) : ℝ :=
  (1 / 2) * ∑ p ∈ plaquettesIn (supBall y ρ₀), ∑ p' ∈ plaquettesIn (supBall y ρ₀),
    κ p p' * ∑ e : Fin 3, imaginaryComponent e (F p) * imaginaryComponent e (F p')
def IsQuadraticInCurvature {n : ℕ} [NeZero n] (σ C c K ρ₀ : ℝ) (G : TorusField n → ℝ) (y : TorusSite n)
    (κ : TorusPlaquette n → TorusPlaquette n → ℝ) : Prop :=
  ∀ (g : TorusSite n → UnitQuaternion) (W : TorusField n) (s : ℝ), 0 ≤ s → 5 * s ≤ σ → IsCold σ W → IsNearIdentity g W y ρ₀ s →
    |G W - kernelQuadraticForm κ y ρ₀ (lieFormCurl (ballLog g W y ρ₀))| ≤ C * K * (s ^ 3 + Real.exp (-(c * ρ₀)))
def localFunctionalQuadraticStatement : Prop :=
  ∀ σ δ c : ℝ, 0 < σ → 0 < δ → 0 < c → ∃ C c' ρ₁ : ℝ, 0 < c' ∧
    ∀ (n : ℕ) [NeZero n] (K ρ₀ : ℝ) (G : TorusField n → ℝ) (y : TorusSite n), ρ₁ ≤ ρ₀ → 2 * ρ₀ + 2 < n → 0 ≤ K →
      IsLocalGaugeFunctional σ K δ c ρ₀ G y →
      ∃ κ : TorusPlaquette n → TorusPlaquette n → ℝ, (∀ p p', κ p p' = κ p' p) ∧
        (∀ p p', ρ₀ < (supDist p.1 y : ℝ) ∨ ρ₀ < (supDist p'.1 y : ℝ) → κ p p' = 0) ∧
        (∀ p p', |κ p p'| ≤ C * K * Real.exp (-(δ / 2 * max (supDist p.1 y : ℝ) (supDist p'.1 y : ℝ)))) ∧
        IsQuadraticInCurvature σ C c' K ρ₀ G y κ
end YangMills.Construction.ResponseInTheExpansion
end
