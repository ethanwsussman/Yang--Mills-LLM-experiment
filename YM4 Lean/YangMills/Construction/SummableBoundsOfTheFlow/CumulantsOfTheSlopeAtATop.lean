import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsOfASlopeAtATop
import YangMills.Construction.SummableBoundsOfTheFlow.ExplicitCumulantsOfMeans
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames Estimates
namespace Cumulants
variable {F : BlockFrame}
structure SlopeCumulantBounds (s a ρA x : ℝ) (m : ℕ) (ρ κ : ℝ) (p : ℝ → ℝ) (φ : LocalFamily)
    (V : F.GaugeField F.top) (Y : F.Cell) (Hf : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ)
    (b₂ b₃ b₄ : ℝ) : Prop where
  covariance : ∀ (j₀ j₁ k : ℕ) (c₀ : Fin j₀ → F.Site F.top × Fin 4) (X₀ : Fin j₀ → imaginaryQuaternions)
    (c₁ : Fin j₁ → F.Site F.top × Fin 4) (X₁ : Fin j₁ → imaginaryQuaternions) (c : Fin k → F.Site F.top × Fin 4),
    j₀ ≤ 2 → j₁ ≤ 2 → AreUnitVectors X₀ → AreUnitVectors X₁ →
    (∀ l, (∃ u, c₀ u = c l) ∨ ∃ u, c₁ u = c l) →
    |ballCovariance (cutoffFactor ρ p) (fun η => interpolatedExponentOfTerms s a ρA x m φ η V)
      (fieldDeriv (Hf) V c₀ X₀) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V c₁ X₁)| ≤
      b₂ * Real.exp (-(κ / 16 * (bondSpan Y c : ℝ)))
  covariance_cells : ∀ (j₀ j₁ k : ℕ) (c₀ : Fin j₀ → F.Site F.top × Fin 4) (X₀ : Fin j₀ → imaginaryQuaternions)
    (c₁ : Fin j₁ → F.Site F.top × Fin 4) (X₁ : Fin j₁ → imaginaryQuaternions) (c : Fin k → F.Site F.top × Fin 4),
    j₀ ≤ 2 → j₁ ≤ 3 → AreUnitVectors X₀ → AreUnitVectors X₁ →
    (∀ l, (∃ u, c₀ u = c l) ∨ ∃ u, c₁ u = c l) →
    |ballCovariance (cutoffFactor ρ p) (fun η => interpolatedExponentOfTerms s a ρA x m φ η V)
      (fieldDeriv (Hf) V c₀ X₀) (fieldDeriv (interpolatedCellExponent s a ρA x m φ) V c₁ X₁)| ≤
      b₂ * Real.exp (-(κ / 16 * (bondSpan Y c : ℝ)))
  third : ∀ (j₀ j₁ j₂ k : ℕ) (c₀ : Fin j₀ → F.Site F.top × Fin 4) (X₀ : Fin j₀ → imaginaryQuaternions)
    (c₁ : Fin j₁ → F.Site F.top × Fin 4) (X₁ : Fin j₁ → imaginaryQuaternions)
    (c₂ : Fin j₂ → F.Site F.top × Fin 4) (X₂ : Fin j₂ → imaginaryQuaternions)
    (c : Fin k → F.Site F.top × Fin 4), j₀ ≤ 2 → j₁ ≤ 2 → j₂ ≤ 2 →
    AreUnitVectors X₀ → AreUnitVectors X₁ → AreUnitVectors X₂ →
    (∀ l, (∃ u, c₀ u = c l) ∨ (∃ u, c₁ u = c l) ∨ ∃ u, c₂ u = c l) →
    |ballThirdCumulant (cutoffFactor ρ p) (fun η => interpolatedExponentOfTerms s a ρA x m φ η V)
      (fieldDeriv (Hf) V c₀ X₀) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V c₁ X₁)
      (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V c₂ X₂)| ≤
      b₃ * Real.exp (-(κ / 16 * (bondSpan Y c : ℝ)))
  fourth : ∀ (j₀ j₁ j₂ j₃ k : ℕ) (c₀ : Fin j₀ → F.Site F.top × Fin 4) (X₀ : Fin j₀ → imaginaryQuaternions)
    (c₁ : Fin j₁ → F.Site F.top × Fin 4) (X₁ : Fin j₁ → imaginaryQuaternions)
    (c₂ : Fin j₂ → F.Site F.top × Fin 4) (X₂ : Fin j₂ → imaginaryQuaternions)
    (c₃ : Fin j₃ → F.Site F.top × Fin 4) (X₃ : Fin j₃ → imaginaryQuaternions) (c : Fin k → F.Site F.top × Fin 4),
    j₀ ≤ 2 → j₁ ≤ 2 → j₂ ≤ 2 → j₃ ≤ 2 →
    AreUnitVectors X₀ → AreUnitVectors X₁ → AreUnitVectors X₂ → AreUnitVectors X₃ →
    (∀ l, (∃ u, c₀ u = c l) ∨ (∃ u, c₁ u = c l) ∨ (∃ u, c₂ u = c l) ∨ ∃ u, c₃ u = c l) →
    |ballFourthCumulant (cutoffFactor ρ p) (fun η => interpolatedExponentOfTerms s a ρA x m φ η V)
      (fieldDeriv (Hf) V c₀ X₀) (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V c₁ X₁)
      (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V c₂ X₂)
      (fieldDeriv (interpolatedExponentOfTerms s a ρA x m φ) V c₃ X₃)| ≤
      b₄ * Real.exp (-(κ / 16 * (bondSpan Y c : ℝ)))
def slopeCumulantsAtTopBound : Prop :=
  ∀ (N N' : ℕ) (κ lam : ℝ), 0 < κ → 0 < lam →
    ∃ B : (ℕ → ℝ) → ℝ, (∀ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) → 0 ≤ B Cq) ∧
      ∀ (F : BlockFrame) (s a ρA x : ℝ) (m : ℕ) (ρ α β : ℝ) (p : ℝ → ℝ) (Cq : ℕ → ℝ) (φ : LocalFamily)
        (V : F.GaugeField F.top), InterpolatedLawAtTop s a ρA x m ρ lam κ β p Cq N N' φ V → 0 ≤ α →
        ∀ (Y : F.Cell) (Hf : StepVariable (finiteCells F) → F.GaugeField F.top → ℝ),
        (∀ (j₀ : ℕ) (c₀ : Fin j₀ → F.Site F.top × Fin 4) (X₀ : Fin j₀ → imaginaryQuaternions), j₀ ≤ 2 →
          AreUnitVectors X₀ → CutoffSlopeBoundAtCell s a ρA x m ρ κ α p Cq φ V Y c₀ (fieldDeriv Hf V c₀ X₀)) →
        SlopeCumulantBounds s a ρA x m ρ κ p φ V Y Hf (B Cq * (α * β)) (B Cq * (α * β ^ 2))
          (B Cq * (α * β ^ 3))
end Cumulants
end YangMills.Construction
end
