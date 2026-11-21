import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionsInTheLawAtATop
import YangMills.Construction.SummableBoundsOfTheFlow.ExplicitCumulantsOfMeans
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Cumulants
open MeasureTheory BlockAverages ColdStepAtMirrorFrames Estimates
variable {F : BlockFrame}
def cellExpansionInField (star : Bool) (a ρA : ℝ) (m : ℕ) (h : LocalFamily) (Y : F.Cell)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  cellCentredExpansion star a ρA m h Y η V
def cellExponentTotal (star : Bool) (a ρA x : ℝ) (m : ℕ) (φ : LocalFamily)
    (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top) : ℝ :=
  ∑ Z : ↥(finiteCells F), cellExponent star a ρA x m Z.1 V η
structure MeanCumulantBounds (star : Bool) (a ρA x : ℝ) (m : ℕ) (ρ κ : ℝ) (p : ℝ → ℝ) (φ h : LocalFamily)
    (V : F.GaugeField F.top) (Y : F.Cell) (b₂ b₃ b₄ : ℝ) : Prop where
  cov_exponent : ∀ (j₀ j₁ k : ℕ) (c₀ : Fin j₀ → F.Site F.top × Fin 4) (X₀ : Fin j₀ → imaginaryQuaternions)
    (c₁ : Fin j₁ → F.Site F.top × Fin 4) (X₁ : Fin j₁ → imaginaryQuaternions) (c : Fin k → F.Site F.top × Fin 4),
    j₀ ≤ 2 → j₁ ≤ 2 → AreUnitVectors X₀ → AreUnitVectors X₁ →
    (∀ l, (∃ i, c₀ i = c l) ∨ ∃ i, c₁ i = c l) →
    |ballCovariance (cutoffFactor ρ p) (fun η => LawAtTop.exponentSum star a ρA x m φ η V)
      (fieldDeriv (cellExpansionInField star a ρA m h Y) V c₀ X₀) (fieldDeriv (LawAtTop.exponentSum star a ρA x m φ) V c₁ X₁)| ≤
      b₂ * Real.exp (-(κ / 16 * (bondSpan Y c : ℝ)))
  cov_cellSum : ∀ (j₀ j₁ k : ℕ) (c₀ : Fin j₀ → F.Site F.top × Fin 4) (X₀ : Fin j₀ → imaginaryQuaternions)
    (c₁ : Fin j₁ → F.Site F.top × Fin 4) (X₁ : Fin j₁ → imaginaryQuaternions) (c : Fin k → F.Site F.top × Fin 4),
    j₀ ≤ 2 → j₁ ≤ 3 → AreUnitVectors X₀ → AreUnitVectors X₁ →
    (∀ l, (∃ i, c₀ i = c l) ∨ ∃ i, c₁ i = c l) →
    |ballCovariance (cutoffFactor ρ p) (fun η => LawAtTop.exponentSum star a ρA x m φ η V)
      (fieldDeriv (cellExpansionInField star a ρA m h Y) V c₀ X₀) (fieldDeriv (cellExponentTotal star a ρA x m φ) V c₁ X₁)| ≤
      b₂ * Real.exp (-(κ / 16 * (bondSpan Y c : ℝ)))
  third : ∀ (j₀ j₁ j₂ k : ℕ) (c₀ : Fin j₀ → F.Site F.top × Fin 4) (X₀ : Fin j₀ → imaginaryQuaternions)
    (c₁ : Fin j₁ → F.Site F.top × Fin 4) (X₁ : Fin j₁ → imaginaryQuaternions)
    (c₂ : Fin j₂ → F.Site F.top × Fin 4) (X₂ : Fin j₂ → imaginaryQuaternions)
    (c : Fin k → F.Site F.top × Fin 4), j₀ ≤ 2 → j₁ ≤ 2 → j₂ ≤ 2 →
    AreUnitVectors X₀ → AreUnitVectors X₁ → AreUnitVectors X₂ →
    (∀ l, (∃ i, c₀ i = c l) ∨ (∃ i, c₁ i = c l) ∨ ∃ i, c₂ i = c l) →
    |ballThirdCumulant (cutoffFactor ρ p) (fun η => LawAtTop.exponentSum star a ρA x m φ η V)
      (fieldDeriv (cellExpansionInField star a ρA m h Y) V c₀ X₀) (fieldDeriv (LawAtTop.exponentSum star a ρA x m φ) V c₁ X₁)
      (fieldDeriv (LawAtTop.exponentSum star a ρA x m φ) V c₂ X₂)| ≤
      b₃ * Real.exp (-(κ / 16 * (bondSpan Y c : ℝ)))
  fourth : ∀ (j₀ j₁ j₂ j₃ k : ℕ) (c₀ : Fin j₀ → F.Site F.top × Fin 4) (X₀ : Fin j₀ → imaginaryQuaternions)
    (c₁ : Fin j₁ → F.Site F.top × Fin 4) (X₁ : Fin j₁ → imaginaryQuaternions)
    (c₂ : Fin j₂ → F.Site F.top × Fin 4) (X₂ : Fin j₂ → imaginaryQuaternions)
    (c₃ : Fin j₃ → F.Site F.top × Fin 4) (X₃ : Fin j₃ → imaginaryQuaternions) (c : Fin k → F.Site F.top × Fin 4),
    j₀ ≤ 2 → j₁ ≤ 2 → j₂ ≤ 2 → j₃ ≤ 2 →
    AreUnitVectors X₀ → AreUnitVectors X₁ → AreUnitVectors X₂ → AreUnitVectors X₃ →
    (∀ l, (∃ i, c₀ i = c l) ∨ (∃ i, c₁ i = c l) ∨ (∃ i, c₂ i = c l) ∨ ∃ i, c₃ i = c l) →
    |ballFourthCumulant (cutoffFactor ρ p) (fun η => LawAtTop.exponentSum star a ρA x m φ η V)
      (fieldDeriv (cellExpansionInField star a ρA m h Y) V c₀ X₀) (fieldDeriv (LawAtTop.exponentSum star a ρA x m φ) V c₁ X₁)
      (fieldDeriv (LawAtTop.exponentSum star a ρA x m φ) V c₂ X₂)
      (fieldDeriv (LawAtTop.exponentSum star a ρA x m φ) V c₃ X₃)| ≤
      b₄ * Real.exp (-(κ / 16 * (bondSpan Y c : ℝ)))
def meanCumulantsAtTopStatement : Prop :=
  ∀ (N N' : ℕ) (κ lam : ℝ), 0 < κ → 0 < lam →
    ∃ B : (ℕ → ℝ) → ℝ, (∀ Cq : ℕ → ℝ, (∀ q, 0 ≤ Cq q) → 0 ≤ B Cq) ∧
      ∀ (F : BlockFrame) (star : Bool) (a ρA x : ℝ) (m : ℕ) (ρ α β : ℝ) (p : ℝ → ℝ) (Cq : ℕ → ℝ)
        (φ h : LocalFamily) (V : F.GaugeField F.top),
        LawAtTop.LawAtTop star a ρA x m ρ lam κ α β p Cq N N' φ h V → ∀ Y : F.Cell,
        MeanCumulantBounds star a ρA x m ρ κ p φ h V Y (B Cq * (α * β)) (B Cq * (α * β ^ 2)) (B Cq * (α * β ^ 3))
end YangMills.Construction.Cumulants
end
