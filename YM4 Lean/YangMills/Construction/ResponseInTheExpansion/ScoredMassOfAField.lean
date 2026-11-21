import YangMills.Construction.ResponseInTheExpansion.ExpansionOfTheResponse
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps StepCosts BlockAverages WeightedResponses
def ScoredMassStatement : Prop :=
  ∀ (ℓ : StepParameters) (t : ℕ) (x : ℝ) (D : TorusFunctional) (f : LocalDensity) (Λ : LabelSpace)
    (Dq : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ)
    (Φ : (n : ℕ) → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → Finset (TorusSite n) → ℝ)
    (φ : (n : ℕ) → TorusSite n → TorusField n → (Y : Finset (TorusSite n)) → (Y → Λ.Ω) → ℝ) (s : Λ.Ω → ℝ),
    ℓ.Admissible → 1 ≤ ℓ.E → 0 < x → 4 * ℓ.n₀ + 2 ^ 16 ≤ clusterRange x → ColdExpansion ℓ t x D f →
    HullExpansion ℓ t x D f Λ Dq Φ φ → PriceBoundsScore ℓ x Λ Φ φ s →
    ∀ (n : ℕ) [NeZero n], IsBlockTorusSide ℓ n → ∀ W : TorusField n,
      (open Classical in ∑ Y ∈ Finset.univ.filter (IsHullState ℓ (clusterRange x) W),
        ∫⁻ ω, ENNReal.ofReal (Dq n W Y ω * Real.exp (∑ y : Y, s (ω y)))
          ∂(Measure.pi fun _ : Y => Λ.μ)) ≤
      ENNReal.ofReal (D n (trivialField n) * 2 ^ Fintype.card (TorusSite n) *
        Real.exp (2 * ℓ.E * Fintype.card (TorusSite n)))
end YangMills.Construction.ResponseInTheExpansion
end
