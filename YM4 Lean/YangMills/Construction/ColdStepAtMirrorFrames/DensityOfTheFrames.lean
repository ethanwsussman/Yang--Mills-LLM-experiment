import YangMills.Construction.ColdStepAtMirrorFrames.FramesAgainstTheLeastField
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def frameDensityFamily (star : Bool) (a ρ x : ℝ) (m : ℕ) : TopLevelFamily :=
  fun _ Y V => frameDensity star a ρ x m Y V
structure FrameDensityBounds (a ρ δ₂ Ct σ δ x : ℝ) (m L t n₀ : ℕ) : Prop where
  localDensity : IsLocalDensity L t n₀ (5 / 4 * σ) (frameDensityFamily false a ρ x m)
  analytic : ∀ F, IsCubicTopTorus L t n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature (5 / 4 * σ) V → IsBondAnalyticAt (frameDensityFamily false a ρ x m F Y) V
  derivDecay : DerivDecay L t n₀ (5 / 4 * σ) (frameDensityFamily false a ρ x m) fun _ n =>
    Ct * x * Real.exp (-(δ₂ / 8 * m)) / torusDecayFactor L δ n
  localOnTori : IsLocalOnTori L t n₀ (5 / 4 * σ) (frameDensityFamily false a ρ x m) fun r =>
    Ct * x * Real.exp (-(δ₂ / 8 * m)) / torusDecayFactor L δ r
  abs_le : ∀ F, IsCubicTopTorus L t n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top),
    IsSmallCurvature (5 / 4 * σ) V →
    |frameDensityFamily false a ρ x m F Y V| ≤ Ct * x * Real.exp (-(δ₂ / 8 * m))
  eq_zero : ∀ F, IsCubicTopTorus L t n₀ F → ∀ star : Bool, (star = true ∨ ¬ ∀ i, 4 * m + 5 < F.extent i) →
    ∀ (Y : F.Cell) (V : F.GaugeField F.top), IsSmallCurvature (5 / 4 * σ) V →
      frameDensityFamily star a ρ x m F Y V = 0
def frameDensityBoundsStatement : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters) (Cf C σ₀ : ℝ), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    FrameBounds a L c Cf C σ₀ → ∃ Ct σ₁ : ℝ, 0 < Ct ∧ 0 < σ₁ ∧ σ₁ ≤ σ₀ ∧
      ∀ (κ δ σ x : ℝ) (m t n₀ : ℕ), 0 < κ → κ ≤ c.δ₂ / 2 ^ 14 → δ = κ / 2 ^ 10 → 0 < σ → σ ≤ σ₁ →
        1 ≤ x → 16 ≤ m → 64 ≤ n₀ → frameDecayBound Cf c.δ₂ m ≤ 2⁻¹ ^ 10 * σ →
        C * x ^ 2 * frameDecayBound Cf c.δ₂ m ≤ Real.exp (-(2 ^ 10 * κ * m)) →
        C * x ^ 2 * Real.exp (-(2 * c.δ₂ * m)) ≤ 1 →
        FrameDensityBounds a c.ρA c.δ₂ Ct σ δ x m L t n₀
end YangMills.Construction.ColdStepAtMirrorFrames
end
